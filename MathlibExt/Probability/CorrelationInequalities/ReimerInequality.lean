/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Reimer
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Extension.Linear

/-!
# Reimer's inequality

We prove Reimer's inequality for arbitrary events and product probability weights on the finite
Boolean cube. The proof uses the butterfly argument and partitions pairs of configurations by
their common coordinates. The linear algebra adapts the archived proofs in
`Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean` and
`Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean`. The proof of the counting bound
`|A □ B| ≤ |A ∩ flipCfg ⁻¹' B|` follows `Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean`
in choosing complementary witnesses and using them to construct the butterfly body.

## Main statements

* `reimer_inequality`: `wprob φ (A □ B) ≤ wprob φ A * wprob φ B` for every product probability
  weight `φ` on `Fin n` and all events `A`, `B`.
* `reimer_wprob_core`: the same statement in the form `StatMech.ReimerWprobCore`. With it,
  `StatMech.reimer_wprob_general_of_core` gives the inequality for product probability weights
  on any finite coordinate set, and `StatMech.reimer_inequality_of_core` for every Bernoulli
  product measure on a finite set.

## References

* D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000),
  27–32.
* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), 556–569.
-/

@[expose] public section

namespace MathlibExt.Probability.ReimerInequalityWanted

open Finset Matrix StatMech

section Butterfly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def tensor {R : Type*} [CommMonoid R] (v : ι → Bool → R) (x : ConfigSpace ι) : R :=
  ∏ i, v i (x i)

private lemma dotProduct_tensor {R : Type*} [CommSemiring R] (v w : ι → Bool → R) :
    tensor v ⬝ᵥ tensor w = ∏ i, v i ⬝ᵥ w i := by
  simp only [dotProduct, tensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i b => v i b * w i b).symm

private def redBit (b : Bool) : Bool → ℝ :=
  fun z => if b ≤ z then 1 else 0

private def yellowBit (b : Bool) : Bool → ℝ :=
  fun z => if z = false then 1 else if b then -1 else 0

private def tipBit : Bool → Bool → Bool → ℤ
  | false, false, z => if z then 0 else 1
  | false, true, _ => 1
  | true, false, z => if z then 1 else 0
  | true, true, z => if z then -1 else 1

-- These are the duals to the two vectors obtained by fixing the first bit of tipBit to false.
private def dualBit : Bool → Bool → ℤ
  | false, z => if z then -1 else 1
  | true, z => if z then 1 else 0

private def redVec (x : ConfigSpace ι) : ConfigSpace ι → ℝ :=
  tensor fun i => redBit (x i)

private def yellowVec (x : ConfigSpace ι) : ConfigSpace ι → ℝ :=
  tensor fun i => yellowBit (x i)

private def tipVec (body tip : ConfigSpace ι) : ConfigSpace ι → ℝ :=
  tensor fun i z => (tipBit (body i) (tip i) z : ℝ)

private lemma dotProduct_red_yellow (x y : ConfigSpace ι) (h : x ≠ y) :
    redVec x ⬝ᵥ yellowVec y = 0 := by
  rw [redVec, yellowVec, dotProduct_tensor]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hx : x i <;> cases hy : y i <;>
    simp [hx, hy] at hi <;>
    norm_num [hx, hy, redBit, yellowBit, dotProduct, Fintype.sum_bool, Bool.le_iff_imp]

private lemma dotProduct_red_yellow_self (x : ConfigSpace ι) :
    redVec x ⬝ᵥ yellowVec x ≠ 0 := by
  rw [redVec, yellowVec, dotProduct_tensor]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases hx : x i <;> norm_num [hx, redBit, yellowBit, dotProduct, Fintype.sum_bool, Bool.le_iff_imp]

private lemma dotProduct_red_tip (x body tip : ConfigSpace ι)
    (h : ¬ ∀ i, x i = body i ∨ x i = tip i) :
    redVec x ⬝ᵥ tipVec body tip = 0 := by
  rw [redVec, tipVec, dotProduct_tensor]
  obtain ⟨i, hi⟩ := not_forall.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hx : x i <;> cases hb : body i <;> cases ht : tip i <;>
    simp [hx, hb, ht] at hi <;>
    norm_num [hx, hb, ht, redBit, tipBit, dotProduct, Fintype.sum_bool, Bool.le_iff_imp]

private lemma dotProduct_yellow_tip (x body tip : ConfigSpace ι)
    (h : ¬ ∀ i, x i = body i ∨ x i = !tip i) :
    yellowVec x ⬝ᵥ tipVec body tip = 0 := by
  rw [yellowVec, tipVec, dotProduct_tensor]
  obtain ⟨i, hi⟩ := not_forall.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hx : x i <;> cases hb : body i <;> cases ht : tip i <;>
    simp [hx, hb, ht] at hi <;>
    norm_num [hx, hb, ht, yellowBit, tipBit, dotProduct, Fintype.sum_bool]

private lemma linearIndependent_of_dual {κ X : Type*} [Finite κ] [Fintype X]
    (v w : κ → X → ℝ) (hoff : ∀ i j, i ≠ j → v i ⬝ᵥ w j = 0)
    (hdiag : ∀ i, v i ⬝ᵥ w i ≠ 0) : LinearIndependent ℝ v := by
  classical
  let _ := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (· ⬝ᵥ w j) hc
  simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hoff i j hij, mul_zero])
    (fun hj => (hj (mem_univ j)).elim)] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag j)

private lemma tipPairing_cast (x y z : ConfigSpace ι) :
    ((∏ i, tipBit (x i) (y i) ⬝ᵥ dualBit (z i) : ℤ) : ℝ) =
      tipVec x y ⬝ᵥ tensor (fun i b => (dualBit (z i) b : ℝ)) := by
  rw [tipVec, dotProduct_tensor]
  simp only [Int.cast_prod, dotProduct, Int.cast_sum, Int.cast_mul]

-- The pairing matrix of the tips with the dual test vectors is triangular modulo two.
private lemma tipMatrix_isUnit (body : ConfigSpace ι → ConfigSpace ι)
    (T : Finset (ConfigSpace ι)) :
    IsUnit (Matrix.of fun (y z : T) => tipVec (body y) y ⬝ᵥ
      tensor (fun i b => (dualBit (z.val i) b : ℝ))) := by
  classical
  let M : Matrix T T ℤ := fun y z =>
    ∏ i, tipBit (body y i) (y.val i) ⬝ᵥ dualBit (z.val i)
  let M₂ : Matrix T T (ZMod 2) := (Int.castRingHom (ZMod 2)).mapMatrix M
  let order : T → LinearExtension (ConfigSpace ι) := fun y => toLinearExtension y.val
  have horder : Function.Injective order := fun _ _ h => Subtype.ext h
  have htri : M₂.BlockTriangular order := by
    intro y z h
    have hnle : ¬ y.val ≤ z.val := fun hle => h.not_ge (toLinearExtension.monotone hle)
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, y.val i ≤ z.val i from hnle)
    change ((M y z : ℤ) : ZMod 2) = 0
    simp only [M, Int.cast_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    generalize body y i = b
    revert hi
    cases b <;> cases y.val i <;> cases z.val i <;> decide
  have hdiag (y : T) : M₂ y y = 1 := by
    change ((M y y : ℤ) : ZMod 2) = 1
    simp only [M, Int.cast_prod]
    apply Finset.prod_eq_one
    intro i _
    cases body y i <;> cases y.val i <;> decide
  have hdet₂ : M₂.det = 1 := by
    rw [htri.det]
    apply Finset.prod_eq_one
    intro a ha
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp ha
    have : Subsingleton {z // order z = a} :=
      ⟨fun p q => Subtype.ext (horder (p.property.trans q.property.symm))⟩
    rw [det_eq_elem_of_subsingleton _ (⟨y, hy⟩ : {z // order z = a})]
    exact hdiag y
  have hdet : M.det ≠ 0 := by
    intro h
    have hmap := RingHom.map_det (Int.castRingHom (ZMod 2)) M
    change ((M.det : ℤ) : ZMod 2) = M₂.det at hmap
    simp [h, hdet₂] at hmap
  have hreal : (Matrix.of fun (y z : T) => tipVec (body y) y ⬝ᵥ
        tensor (fun i b => (dualBit (z.val i) b : ℝ))) =
      (Int.castRingHom ℝ).mapMatrix M := by
    ext y z
    exact (tipPairing_cast (body y) y.val z.val).symm
  rw [hreal, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, isUnit_iff_ne_zero]
  change (M.det : ℝ) ≠ 0
  exact_mod_cast hdet

omit [DecidableEq ι] in
private lemma linearIndependent_tip (body : ConfigSpace ι → ConfigSpace ι)
    (T : Finset (ConfigSpace ι)) :
    LinearIndependent ℝ (fun y : T => tipVec (body y) y) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let M : Matrix T T ℝ := fun y z =>
    tipVec (body y) y ⬝ᵥ tensor (fun i b => (dualBit (z.val i) b : ℝ))
  have hM : IsUnit M := tipMatrix_isUnit body T
  have hvec : c ᵥ* M = 0 := by
    funext z
    have h := congrArg (· ⬝ᵥ tensor (fun i b => (dualBit (z.val i) b : ℝ))) hc
    simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
    simpa only [vecMul, dotProduct, M, Pi.zero_apply] using h
  have hzero : c = 0 := Matrix.vecMul_injective_iff_isUnit.mpr hM (by simpa using hvec)
  simp [hzero]

private lemma dotProduct_span {X κ κ' : Type*} [Fintype X] {v : κ → X → ℝ}
    {w : κ' → X → ℝ} (h : ∀ i j, v i ⬝ᵥ w j = 0) {x y : X → ℝ}
    (hx : x ∈ Submodule.span ℝ (Set.range v)) (hy : y ∈ Submodule.span ℝ (Set.range w)) :
    x ⬝ᵥ y = 0 := by
  have hv (i : κ) : v i ⬝ᵥ y = 0 := by
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact h i j
    | zero => simp
    | add z z' _ _ hz hz' => simp [dotProduct_add, hz, hz']
    | smul c z _ hz => simp [dotProduct_smul, hz]
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hv i
  | zero => simp
  | add z z' _ _ hz hz' => simp [add_dotProduct, hz, hz']
  | smul c z _ hz => simp [smul_dotProduct, hz]

private lemma linearIndependent_sum_of_orthogonal {X κ κ' : Type*} [Fintype X]
    {v : κ → X → ℝ} {w : κ' → X → ℝ} (hv : LinearIndependent ℝ v)
    (hw : LinearIndependent ℝ w) (h : ∀ i j, v i ⬝ᵥ w j = 0) :
    LinearIndependent ℝ (Sum.elim v w) := by
  apply linearIndependent_sum.mpr
  refine ⟨hv, hw, ?_⟩
  rw [Submodule.disjoint_def]
  intro x hx hy
  exact dotProduct_self_eq_zero.mp (dotProduct_span h hx hy)

open Classical in
-- The two unused portions of the cube supply independent vectors orthogonal to the tips.
private lemma card_disjointOccurrence_le_card_inter_flip (A B : Set (ConfigSpace ι)) :
    (Finset.univ.filter (· ∈ disjointOccurrence A B)).card ≤
      (Finset.univ.filter (fun x => x ∈ A ∧ flipCfg x ∈ B)).card := by
  let T : Finset (ConfigSpace ι) := Finset.univ.filter (· ∈ disjointOccurrence A B)
  let R : Finset (ConfigSpace ι) := Finset.univ.filter (· ∈ A)
  let Y : Finset (ConfigSpace ι) := Finset.univ.filter (fun x => flipCfg x ∈ B)
  have hwitness (y : T) : ∃ K : Set ι, OccursOn A K y ∧ OccursOn B Kᶜ y := by
    obtain ⟨K, L, hd, hA, hB⟩ := mem_disjointOccurrence.mp (Finset.mem_filter.mp y.2).2
    exact ⟨K, hA, hB.mono (Set.disjoint_left.mp hd.symm)⟩
  let body (y : ConfigSpace ι) : ConfigSpace ι :=
    if hy : y ∈ T then fun i => if i ∈ (hwitness ⟨y, hy⟩).choose then y i else !y i
    else y
  have hred (x : ↥(Rᶜ)) (y : T) : redVec x.val ⬝ᵥ tipVec (body y) y = 0 := by
    apply dotProduct_red_tip
    intro h
    let K := (hwitness y).choose
    have hx : x.val ∈ A := (hwitness y).choose_spec.1 x fun i hi => by
      simpa [body, y.property, K, hi] using h i
    exact (Finset.mem_compl.mp x.property) (Finset.mem_filter.mpr ⟨mem_univ _, hx⟩)
  have hyellow (x : ↥(R \ Y)) (y : T) : yellowVec x.val ⬝ᵥ tipVec (body y) y = 0 := by
    apply dotProduct_yellow_tip
    intro h
    let K := (hwitness y).choose
    have hx : flipCfg x.val ∈ B := (hwitness y).choose_spec.2 (flipCfg x.val) fun i hi => by
      have hi' : i ∉ K := hi
      have he : x.val i = !y.val i := by simpa [body, y.property, K, hi'] using h i
      simp [he]
    exact (Finset.mem_sdiff.mp x.property).2 (Finset.mem_filter.mpr ⟨mem_univ _, hx⟩)
  have hr : LinearIndependent ℝ (fun x : ↥(Rᶜ) => redVec x.val) :=
    linearIndependent_of_dual _ (fun x : ↥(Rᶜ) => yellowVec x.val)
      (fun i j h => dotProduct_red_yellow _ _ (Subtype.val_injective.ne h))
      (fun i => dotProduct_red_yellow_self i.val)
  have hy : LinearIndependent ℝ (fun x : ↥(R \ Y) => yellowVec x.val) :=
    linearIndependent_of_dual _ (fun x : ↥(R \ Y) => redVec x.val)
      (fun i j h => by rw [dotProduct_comm]; exact
        dotProduct_red_yellow _ _ (Subtype.val_injective.ne h.symm))
      (fun i => by rw [dotProduct_comm]; exact dotProduct_red_yellow_self i.val)
  have hry : LinearIndependent ℝ
      (Sum.elim (fun x : ↥(Rᶜ) => redVec x.val) (fun x : ↥(R \ Y) => yellowVec x.val)) :=
    linearIndependent_sum_of_orthogonal hr hy fun r y => dotProduct_red_yellow _ _ fun h =>
      (Finset.mem_compl.mp r.property) (h ▸ (Finset.mem_sdiff.mp y.property).1)
  have hall := linearIndependent_sum_of_orthogonal hry (linearIndependent_tip body T)
    (fun x y => Sum.recOn x (fun r => hred r y) (fun s => hyellow s y))
  have hcard := hall.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum] at hcard
  simp only [Fintype.card_coe, Finset.card_compl] at hcard
  have hsplit := Finset.card_sdiff_add_card_inter R Y
  have hR : R.card ≤ Fintype.card (ConfigSpace ι) := Finset.card_le_univ R
  have hRY : R ∩ Y = Finset.univ.filter (fun x => x ∈ A ∧ flipCfg x ∈ B) := by
    ext x
    simp [R, Y]
  rw [← hRY]
  change T.card ≤ _
  omega

end Butterfly

section Cells

variable {ι : Type*}

-- A cell fixes the common bits of the two configurations. The remaining bits are opposite.
private def pairPattern (p : ConfigSpace ι × ConfigSpace ι) (i : ι) : Option Bool :=
  if p.1 i = p.2 i then some (p.1 i) else none

private def fill (k : ι → Option Bool) (x : ConfigSpace {i // k i = none}) :
    ConfigSpace ι :=
  fun i => if hi : k i = none then x ⟨i, hi⟩ else (k i).getD false

private def cellPair (k : ι → Option Bool) (x : ConfigSpace {i // k i = none}) :
    ConfigSpace ι × ConfigSpace ι :=
  (fill k x, fill k (flipCfg x))

private lemma pairPattern_cellPair (k : ι → Option Bool) (x : ConfigSpace {i // k i = none}) :
    pairPattern (cellPair k x) = k := by
  funext i
  cases hi : k i with
  | none =>
    have hn : x ⟨i, hi⟩ ≠ !x ⟨i, hi⟩ := by cases x ⟨i, hi⟩ <;> decide
    simp [pairPattern, cellPair, fill, hi, hn]
  | some b => simp [pairPattern, cellPair, fill, hi]

private lemma cellPair_pairPattern (p : ConfigSpace ι × ConfigSpace ι) :
    cellPair (pairPattern p) (fun i => p.1 i.val) = p := by
  apply Prod.ext <;> funext i
  · by_cases h : p.1 i = p.2 i <;> simp [cellPair, fill, pairPattern, h]
  · by_cases h : p.1 i = p.2 i
    · simp [cellPair, fill, pairPattern, h]
    · have he : p.1 i = !(p.2 i) := by
        cases h₁ : p.1 i <;> cases h₂ : p.2 i <;> simp_all
      simpa [cellPair, fill, pairPattern, h] using he

private noncomputable def cellEquiv :
    (Σ k : ι → Option Bool, ConfigSpace {i // k i = none}) ≃
      ConfigSpace ι × ConfigSpace ι := by
  refine Equiv.ofBijective (fun p => cellPair p.1 p.2) ⟨?_, ?_⟩
  · intro ⟨k, x⟩ ⟨l, y⟩ h
    have hkl : k = l := by simpa only [pairPattern_cellPair] using congrArg pairPattern h
    subst l
    congr 1
    funext i
    have hi := congrArg (fun p : ConfigSpace ι × ConfigSpace ι => p.1 i.val) h
    simpa [cellPair, fill, i.property] using hi
  · intro p
    exact ⟨⟨pairPattern p, fun i => p.1 i.val⟩, cellPair_pairPattern p⟩

private lemma disjointOccurrence_fill (k : ι → Option Bool)
    (A B : Set (ConfigSpace ι)) (x : ConfigSpace {i // k i = none})
    (hx : fill k x ∈ disjointOccurrence A B) :
    x ∈ disjointOccurrence (fill k ⁻¹' A) (fill k ⁻¹' B) := by
  obtain ⟨K, L, hd, hA, hB⟩ := mem_disjointOccurrence.mp hx
  have hfill {S : Set ι} {y : ConfigSpace {i // k i = none}}
      (h : agreeOn (Subtype.val ⁻¹' S) x y) : agreeOn S (fill k x) (fill k y) := by
    intro i hi
    by_cases hk : k i = none
    · simpa [fill, hk] using h ⟨i, hk⟩ hi
    · simp [fill, hk]
  exact ⟨Subtype.val ⁻¹' K, Subtype.val ⁻¹' L, hd.preimage _,
    fun _ hy => hA _ (hfill hy), fun _ hy => hB _ (hfill hy)⟩

variable [Fintype ι]

private lemma cellWeight_eq (φ : ι → Bool → ℝ) (k : ι → Option Bool)
    (x y : ConfigSpace {i // k i = none}) :
    pweight φ (fill k x) * pweight φ (fill k (flipCfg x)) =
      pweight φ (fill k y) * pweight φ (fill k (flipCfg y)) := by
  simp only [pweight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : k i = none
  · cases hx : x ⟨i, hi⟩ <;> cases hy : y ⟨i, hi⟩ <;>
      simp [fill, hi, hx, hy, mul_comm]
  · simp [fill, hi]

variable [DecidableEq ι]

open Classical in
private lemma sum_pair_weight (φ : ι → Bool → ℝ) (A B : Set (ConfigSpace ι)) :
    (∑ p : ConfigSpace ι × ConfigSpace ι,
      if p.1 ∈ A ∧ p.2 ∈ B then pweight φ p.1 * pweight φ p.2 else 0) =
      wprob φ A * wprob φ B := by
  rw [Fintype.sum_prod_type, wprob, wprob, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ B <;> simp [Set.indicator, ha, hb]

open Classical in
private lemma sum_cell_weight_le (φ : ι → Bool → ℝ) (hφ : ∀ i b, 0 ≤ φ i b)
    (A B : Set (ConfigSpace ι)) (k : ι → Option Bool) :
    (∑ x : ConfigSpace {i // k i = none},
      if fill k x ∈ disjointOccurrence A B then
        pweight φ (fill k x) * pweight φ (fill k (flipCfg x)) else 0) ≤
    (∑ x : ConfigSpace {i // k i = none},
      if fill k x ∈ A ∧ fill k (flipCfg x) ∈ B then
        pweight φ (fill k x) * pweight φ (fill k (flipCfg x)) else 0) := by
  let z : ConfigSpace {i // k i = none} := fun _ => false
  let c : ℝ := pweight φ (fill k z) * pweight φ (fill k (flipCfg z))
  have hc : 0 ≤ c := mul_nonneg (pweight_nonneg hφ _) (pweight_nonneg hφ _)
  simp only [cellWeight_eq φ k _ z, ← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  have hsubset : Finset.univ.filter (fun x => fill k x ∈ disjointOccurrence A B) ⊆
      Finset.univ.filter (· ∈ disjointOccurrence (fill k ⁻¹' A) (fill k ⁻¹' B)) :=
    fun x hx => Finset.mem_filter.mpr
      ⟨mem_univ _, disjointOccurrence_fill k A B x (Finset.mem_filter.mp hx).2⟩
  exact_mod_cast (Finset.card_le_card hsubset).trans
    (card_disjointOccurrence_le_card_inter_flip (fill k ⁻¹' A) (fill k ⁻¹' B))

end Cells

/-- **Reimer's inequality** (van den Berg–Kesten conjecture). For every `n`, every product
probability weight `φ` on `{0, 1}^n` (`φ i b ≥ 0`, `φ i false + φ i true = 1`) and all events
`A`, `B ⊆ {0, 1}^n`, `P(A □ B) ≤ P(A) P(B)`, where `A □ B` is the event that `A` and `B` occur on
disjoint sets of coordinates.

Source: D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9
(2000), 27–32. -/
theorem reimer_inequality :
    ∀ (n : ℕ) (φ : Fin n → Bool → ℝ),
      (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
      ∀ (A B : Set (ConfigSpace (Fin n))),
        wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  intro n φ hφ0 hφ1 A B
  have huniv : wprob φ Set.univ = 1 := by
    simpa [wprob] using sum_pweight_eq_one hφ1
  calc
    wprob φ (disjointOccurrence A B) =
        ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
          if p.1 ∈ disjointOccurrence A B then
            pweight φ p.1 * pweight φ p.2 else 0 := by
      simpa only [Set.mem_univ, and_true, huniv, mul_one] using
        (sum_pair_weight φ (disjointOccurrence A B) Set.univ).symm
    _ ≤ ∑ p : ConfigSpace (Fin n) × ConfigSpace (Fin n),
          if p.1 ∈ A ∧ p.2 ∈ B then pweight φ p.1 * pweight φ p.2 else 0 := by
      rw [← cellEquiv.sum_comp, ← cellEquiv.sum_comp
        (fun p : ConfigSpace (Fin n) × ConfigSpace (Fin n) =>
          if p.1 ∈ A ∧ p.2 ∈ B then pweight φ p.1 * pweight φ p.2 else 0)]
      simp only [Fintype.sum_sigma]
      exact Finset.sum_le_sum (fun k _ => sum_cell_weight_le φ hφ0 A B k)
    _ = wprob φ A * wprob φ B := sum_pair_weight φ A B

/-- Reimer's inequality in the form of the ported hypothesis `StatMech.ReimerWprobCore`
(definitionally `reimer_inequality`).

Source: D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9
(2000), 27–32. -/
theorem reimer_wprob_core : ReimerWprobCore :=
  reimer_inequality

end MathlibExt.Probability.ReimerInequalityWanted
