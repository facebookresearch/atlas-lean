/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Finsupp
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Subgroups of free groups with normal derived subgroup (Kourovka Notebook Problem 11.124)

Kourovka Notebook, Problem 11.124 (V. E. Shpilrain): let `F` be a non-cyclic free group and `R` a
non-cyclic subgroup of `F`. If `[R, R]` is normal in `F`, is `R` normal in `F`?

We prove that a non-cyclic subgroup with normal derived subgroup is normal. The proof uses
weights on edges of Schreier graphs to detect elements in subgroup abelianizations.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.124 (V. E. Shpilrain). UnsolvedMath
record UM-00700816 (`KOU-11.124`), dataset ulamai/UnsolvedMath v1.8.0.

The free group `F` is `FreeGroup α` on an arbitrary basis `α : Type` (any rank, as in the resolving
paper); non-cyclic is `¬ IsCyclic`. `[R, R]` is the commutator subgroup `⁅R, R⁆`, taken in `F`.
-/

namespace MathlibExt.GroupTheory.FreeGroupDerivedNormalSubgroupKourovka11Problem124Wanted

/-- **Kourovka Problem 11.124 (free-group subgroups with normal derived subgroup).** The
statement that for every set $X$ such that the free group $F$ on $X$ is not cyclic, every subgroup
$R$ of $F$ that is not cyclic and whose derived subgroup $[R, R]$ is normal in $F$ is itself
normal in $F$. -/
@[expose] public def derivedNormalImpliesNormal : Prop :=
  ∀ (α : Type), ¬ IsCyclic (FreeGroup α) → ∀ R : Subgroup (FreeGroup α), ¬ IsCyclic R →
    (⁅R, R⁆).Normal → R.Normal

open scoped commutatorElement

noncomputable section

private abbrev generator {G : Type} [Group G] [IsFreeGroup G] :=
  @IsFreeGroup.of G _ _

section EdgeWeights

variable {G V W : Type} [Group G] [IsFreeGroup G] [MulAction G V] [MulAction G W]

-- The two coordinates record the weight of a path by its terminal vertex and its group element.
private def edgeLift (a : IsFreeGroup.Generators G → V → ℚ) :
    G →* (V → Multiplicative ℚ) ⋊[mulAutArrow] G :=
  IsFreeGroup.lift fun i ↦
    ⟨fun v ↦ Multiplicative.ofAdd (a i ((generator i : G)⁻¹ • v)), generator i⟩

private theorem edgeLift_right (a : IsFreeGroup.Generators G → V → ℚ) (g : G) :
    (edgeLift a g).right = g := by
  change (SemidirectProduct.rightHom.comp (edgeLift a)) g = MonoidHom.id G g
  congr 1
  exact IsFreeGroup.ext_hom fun i ↦ by simp [edgeLift, generator, IsFreeGroup.lift_of]

private def walkWeight (a : IsFreeGroup.Generators G → V → ℚ) (g : G) (v : V) : ℚ :=
  ((edgeLift a g).left (g • v)).toAdd

private theorem walkWeight_of (a : IsFreeGroup.Generators G → V → ℚ)
    (i : IsFreeGroup.Generators G) (v : V) :
    walkWeight a (generator i) v = a i v := by
  simp [walkWeight, edgeLift, generator, IsFreeGroup.lift_of]

private theorem walkWeight_one (a : IsFreeGroup.Generators G → V → ℚ) (v : V) :
    walkWeight a 1 v = 0 := by
  simp [walkWeight, SemidirectProduct.one_left]

private theorem walkWeight_mul (a : IsFreeGroup.Generators G → V → ℚ) (g h : G) (v : V) :
    walkWeight a (g * h) v = walkWeight a g (h • v) + walkWeight a h v := by
  simp only [walkWeight, map_mul, SemidirectProduct.mul_left, edgeLift_right,
    Pi.mul_apply, mulAutArrow_apply_apply]
  change (((edgeLift a g).left ((g * h) • v)).toAdd +
    ((edgeLift a h).left (g⁻¹ • ((g * h) • v))).toAdd) = _
  rw [mul_smul, inv_smul_smul]

private theorem walkWeight_inv (a : IsFreeGroup.Generators G → V → ℚ) (g : G) (v : V) :
    walkWeight a g⁻¹ v = -walkWeight a g (g⁻¹ • v) := by
  simpa [walkWeight_one, eq_neg_iff_add_eq_zero, add_comm] using
    (walkWeight_mul a g g⁻¹ v).symm

private theorem free_induction {P : G → Prop} (g : G) (h₁ : P 1)
    (hgen : ∀ i : IsFreeGroup.Generators G, P (generator i))
    (hinv : ∀ g, P g → P g⁻¹) (hmul : ∀ g h, P g → P h → P (g * h)) : P g := by
  let e := IsFreeGroup.mulEquiv G
  suffices ∀ x : FreeGroup (IsFreeGroup.Generators G), P (e x) by simpa using this (e.symm g)
  intro x
  induction x using FreeGroup.induction_on with
  | one => simpa using h₁
  | of i => exact hgen i
  | inv_of a ih => simpa only [map_inv] using hinv _ ih
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb

private theorem walkWeight_unique (a : IsFreeGroup.Generators G → V → ℚ)
    (d : G → V → ℚ) (hmul : ∀ g h v, d (g * h) v = d g (h • v) + d h v)
    (hgen : ∀ i v, d (generator i) v = a i v) (g : G) (v : V) :
    walkWeight a g v = d g v := by
  have hzero (t : V) : d 1 t = 0 := by
    have h := hmul 1 1 t
    simp only [one_mul, one_smul] at h
    linarith
  refine free_induction (P := fun g ↦ ∀ v, walkWeight a g v = d g v) g ?_ ?_ ?_ ?_ v
  · intro t
    rw [walkWeight_one, hzero]
  · intro i t
    rw [walkWeight_of, hgen]
  · intro h ih t
    rw [walkWeight_inv, ih]
    have hh := hmul h h⁻¹ t
    rw [mul_inv_cancel, hzero] at hh
    linarith
  · intro h k ih ik t
    rw [walkWeight_mul, hmul, ih, ik]

private theorem walkWeight_natural (p : V → W) (hp : ∀ (g : G) v, p (g • v) = g • p v)
    (a : IsFreeGroup.Generators G → W → ℚ) (g : G) (v : V) :
    walkWeight (fun i w ↦ a i (p w)) g v = walkWeight a g (p v) := by
  refine walkWeight_unique _ (fun g v ↦ walkWeight a g (p v)) ?_ ?_ g v
  · intro x y w
    rw [walkWeight_mul, hp]
  · simp only [walkWeight_of, implies_true]

-- Only finitely many vertices are visited by a fixed path.
private theorem finite_vertices (g : G) (v : V) :
    ∃ S : Finset V, ∀ a b : IsFreeGroup.Generators G → V → ℚ,
      (∀ i w, w ∈ S → a i w = b i w) → walkWeight a g v = walkWeight b g v := by
  classical
  refine free_induction (P := fun g ↦ ∀ v, ∃ S : Finset V, ∀ a b : IsFreeGroup.Generators G → V → ℚ,
    (∀ i w, w ∈ S → a i w = b i w) → walkWeight a g v = walkWeight b g v) g ?_ ?_ ?_ ?_ v
  · exact fun v ↦ ⟨∅, by simp [walkWeight_one]⟩
  · exact fun i v ↦ ⟨{v}, fun a b h ↦ by simpa only [walkWeight_of] using h i v (by simp)⟩
  · intro g hg v
    obtain ⟨S, hS⟩ := hg (g⁻¹ • v)
    exact ⟨S, fun a b h ↦ by rw [walkWeight_inv, walkWeight_inv, hS a b h]⟩
  · intro g h hg hh v
    obtain ⟨S, hS⟩ := hg (h • v)
    obtain ⟨T, hT⟩ := hh v
    refine ⟨S ∪ T, fun a b he ↦ ?_⟩
    rw [walkWeight_mul, walkWeight_mul, hS a b, hT a b]
    · exact fun i w hw ↦ he i w (Finset.mem_union_right S hw)
    · exact fun i w hw ↦ he i w (Finset.mem_union_left T hw)

-- For weights supported on finitely many vertices, a fixed word has nonzero weight
-- from only finitely many starting vertices.
private theorem finite_starting_vertices (a : IsFreeGroup.Generators G → V → ℚ)
    (S : Finset V) (ha : ∀ i v, v ∉ S → a i v = 0) (g : G) :
    {v : V | walkWeight a g v ≠ 0}.Finite := by
  classical
  refine free_induction (P := fun g ↦ {v : V | walkWeight a g v ≠ 0}.Finite) g ?_ ?_ ?_ ?_
  · simp [walkWeight_one]
  · intro i
    exact S.finite_toSet.subset fun v hv ↦ by
      rw [Set.mem_ofPred_eq, walkWeight_of] at hv
      by_contra h
      exact hv (ha i v h)
  · intro g hg
    apply (hg.preimage (MulAction.toPerm g⁻¹).injective.injOn).subset
    intro v hv
    simpa [walkWeight_inv] using hv
  · intro g h hg hh
    apply ((hg.preimage (MulAction.toPerm h).injective.injOn).union hh).subset
    intro v hv
    simp only [Set.mem_ofPred_eq, walkWeight_mul] at hv
    change walkWeight a g (h • v) ≠ 0 ∨ walkWeight a h v ≠ 0
    exact not_and_or.mp fun ⟨ha, hb⟩ ↦ hv (by rw [ha, hb, add_zero])

end EdgeWeights

section Cosets

variable {G : Type} [Group G]

private abbrev base (H : Subgroup G) : G ⧸ H := QuotientGroup.mk (1 : G)

private theorem smul_base (H : Subgroup G) (g : G) : g • base H = QuotientGroup.mk g := by
  rw [base, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

private theorem fixes_base_iff (H : Subgroup G) (g : G) : g • base H = base H ↔ g ∈ H := by
  rw [smul_base, QuotientGroup.eq]
  simp

variable [IsFreeGroup G]

private def loopHom (H : Subgroup G) (a : IsFreeGroup.Generators G → (G ⧸ H) → ℚ) :
    H →* Multiplicative ℚ where
  toFun h := Multiplicative.ofAdd (walkWeight a (h : G) (base H))
  map_one' := congrArg Multiplicative.ofAdd (walkWeight_one a (base H))
  map_mul' g h := by
    change Multiplicative.ofAdd (walkWeight a ((g : G) * (h : G)) (base H)) = _
    rw [walkWeight_mul, (fixes_base_iff H h).2 h.2]
    rfl

private theorem walkWeight_zero_of_mem_derived {H : Subgroup G}
    (a : IsFreeGroup.Generators G → (G ⧸ H) → ℚ) {c : G} (hc : c ∈ ⁅H, H⁆) :
    walkWeight a c (base H) = 0 := by
  rw [← H.map_subtype_commutator] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  exact congrArg Multiplicative.toAdd (Group.Abelianization.commutator_le_ker (loopHom H a) hx)

-- The abelianization of a free group has a basis over ℤ, so a coordinate separates
-- any nonzero element, and positive powers are injective.
private def abelianCoords (G : Type) [Group G] [IsFreeGroup G] :
    Additive (Group.Abelianization G) ≃+ (IsFreeGroup.Generators G →₀ ℤ) :=
  (IsFreeGroup.toFreeGroup G).abelianizationCongr.toAdditive.trans
    (FreeAbelianGroup.equivFinsupp _)

private theorem exists_character {x : G} (hx : x ∉ _root_.commutator G) :
    ∃ f : G →* Multiplicative ℚ, (f x).toAdd ≠ 0 := by
  classical
  have hab : Group.Abelianization.of x ≠ 1 := fun h ↦ hx (Group.Abelianization.ker_of (G := G) ▸ h)
  let e := abelianCoords G
  have he : e (Additive.ofMul (Group.Abelianization.of x)) ≠ 0 := by
    intro hz
    apply hab
    exact e.injective (hz.trans e.map_zero.symm)
  obtain ⟨i, hi⟩ : ∃ i, e (Additive.ofMul (Group.Abelianization.of x)) i ≠ 0 := by
    contrapose! he
    ext j
    simpa using he j
  let f : Additive (Group.Abelianization G) →+ ℚ :=
    { toFun := fun g ↦ (e g i : ℚ)
      map_zero' := by simp
      map_add' g h := by simp }
  refine ⟨f.toMultiplicative.comp Group.Abelianization.of, ?_⟩
  change (↑(e (Additive.ofMul (Group.Abelianization.of x)) i) : ℚ) ≠ 0
  exact_mod_cast hi

private theorem abelian_pow_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun x : Group.Abelianization G ↦ x ^ n) := by
  intro x y h
  let e := abelianCoords G
  have he : n • e (Additive.ofMul x) = n • e (Additive.ofMul y) := by
    have h' : n • (Additive.ofMul x) = n • (Additive.ofMul y) := h
    simpa only [map_nsmul] using congrArg (fun z : Additive (Group.Abelianization G) ↦ e z) h'
  change Additive.ofMul x = Additive.ofMul y
  apply e.injective
  ext i
  have hi := congrArg (fun f : IsFreeGroup.Generators G →₀ ℤ ↦ f i) he
  simp only [Finsupp.nsmul_apply, nsmul_eq_mul] at hi
  exact mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne') hi

omit [IsFreeGroup G] in
private def representative (H : Subgroup G) (v : G ⧸ H) : G :=
  @ite _ (v = base H) (Classical.propDecidable _) 1 v.out

omit [IsFreeGroup G] in
private theorem mk_representative (H : Subgroup G) (v : G ⧸ H) :
    QuotientGroup.mk (representative H v) = v := by
  classical
  unfold representative
  split
  · exact ‹v = base H›.symm
  · exact QuotientGroup.out_eq' v

omit [IsFreeGroup G] in
private def loopPart (H : Subgroup G) (g : G) (v : G ⧸ H) : H :=
  ⟨(representative H (g • v))⁻¹ * g * representative H v, by
    rw [mul_assoc, ← QuotientGroup.eq, mk_representative, ← smul_eq_mul,
      ← MulAction.Quotient.smul_mk, mk_representative]⟩

omit [IsFreeGroup G] in
private theorem loopPart_mul (H : Subgroup G) (g h : G) (v : G ⧸ H) :
    loopPart H (g * h) v = loopPart H g (h • v) * loopPart H h v := by
  apply Subtype.ext
  simp only [loopPart, Subgroup.coe_mul, mul_smul]
  group

private theorem weight_detects_loop {H : Subgroup G} {c : G} (hc : c ∈ H) (hd : c ∉ ⁅H, H⁆) :
    ∃ a : IsFreeGroup.Generators G → (G ⧸ H) → ℚ, walkWeight a c (base H) ≠ 0 := by
  classical
  let x : H := ⟨c, hc⟩
  obtain ⟨f, hf⟩ := exists_character (x := x) (fun hx ↦
    hd (H.map_subtype_commutator ▸ Subgroup.mem_map_of_mem H.subtype hx))
  let d (g : G) (v : G ⧸ H) := (f (loopPart H g v)).toAdd
  have hbase : loopPart H c (base H) = x := by
    apply Subtype.ext
    simp [loopPart, (fixes_base_iff H c).2 hc, representative, x]
  refine ⟨fun i v ↦ d (generator i) v, ?_⟩
  rw [walkWeight_unique _ d (fun g h v ↦ by dsimp [d]; rw [loopPart_mul, map_mul]; rfl)
    (fun _ _ ↦ rfl)]
  simpa [d, hbase] using hf

-- If a loop commutes modulo the derived subgroup, reading it at any vertex yields
-- the same weight as reading it at the base vertex.
private theorem weight_constant_of_central {H : Subgroup G}
    (a : IsFreeGroup.Generators G → (G ⧸ H) → ℚ) {c : G} (hc : c ∈ H)
    (hcentral : ∀ g : G, ⁅g, c⁆ ∈ ⁅H, H⁆) (v : G ⧸ H) :
    walkWeight a c v = walkWeight a c (base H) := by
  let g := v.out
  have hv : g • base H = v := (smul_base H g).trans (QuotientGroup.out_eq' v)
  have hconj : g⁻¹ * c * g ∈ H := by
    have h : g⁻¹ * c * g = ⁅g⁻¹, c⁆ * c := by rw [commutatorElement_def, inv_inv]; group
    rw [h]
    exact H.mul_mem (H.commutator_le_self (hcentral _)) hc
  have hfix : c • (g • base H) = g • base H := by
    have h := congrArg (fun w : G ⧸ H ↦ g • w)
      ((fixes_base_iff H (g⁻¹ * c * g)).2 hconj)
    simpa only [mul_smul, ← mul_smul g g⁻¹, mul_inv_cancel, one_smul] using h
  have h₁ : walkWeight a (g⁻¹ * c * g) (base H) = walkWeight a c (base H) := by
    have he : g⁻¹ * c * g = ⁅g⁻¹, c⁆ * c := by rw [commutatorElement_def, inv_inv]; group
    rw [he, walkWeight_mul, (fixes_base_iff H c).2 hc,
      walkWeight_zero_of_mem_derived a (hcentral _), zero_add]
  rw [walkWeight_mul, walkWeight_mul, hfix, walkWeight_inv, inv_smul_smul] at h₁
  rw [← hv]
  linarith

private theorem finiteIndex_of_central {H : Subgroup G} {c : G} (hc : c ∈ H)
    (hd : c ∉ ⁅H, H⁆) (hcentral : ∀ g : G, ⁅g, c⁆ ∈ ⁅H, H⁆) : H.FiniteIndex := by
  classical
  obtain ⟨a, ha⟩ := weight_detects_loop hc hd
  obtain ⟨S, hS⟩ := finite_vertices c (base H)
  let b i v := if v ∈ S then a i v else 0
  have hb : walkWeight b c (base H) ≠ 0 :=
    (hS b a fun i w hw ↦ ite_eq_left hw).trans_ne ha
  have hu : {v : G ⧸ H | walkWeight b c v ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun v ↦ by
      change walkWeight b c v ≠ 0
      rwa [weight_constant_of_central b hc hcentral]
  have hf := finite_starting_vertices b S (fun i v hv ↦ ite_eq_right hv) c
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  exact Subgroup.finiteIndex_of_finite_quotient

end Cosets

section Comparison

variable {G : Type} [Group G] [IsFreeGroup G]

private theorem weight_pow_of_invariant {V : Type} [MulAction G V]
    (a : IsFreeGroup.Generators G → V → ℚ) {g : G}
    (hinv : ∀ v, walkWeight a g (g • v) = walkWeight a g v) (n : ℕ) (v : V) :
    walkWeight a (g ^ n) v = (n : ℚ) * walkWeight a g v := by
  induction n generalizing v with
  | zero => simp [walkWeight_one]
  | succ n ih =>
    rw [pow_succ, walkWeight_mul, ih, hinv, Nat.cast_succ, add_mul, one_mul]

private theorem weight_eq_of_central_powers {H : Subgroup G}
    (hp : ∀ g : G, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H ∧ ∀ k : G, ⁅k, g ^ n⁆ ∈ ⁅H, H⁆)
    (a : IsFreeGroup.Generators G → (G ⧸ H) → ℚ) {g : G}
    (hinv : ∀ v, walkWeight a g (g • v) = walkWeight a g v) (v : G ⧸ H) :
    walkWeight a g v = walkWeight a g (base H) := by
  obtain ⟨n, hn, hh, hc⟩ := hp g
  have h := weight_constant_of_central a hh hc v
  rw [weight_pow_of_invariant a hinv, weight_pow_of_invariant a hinv] at h
  exact mul_left_cancel₀ (show (n : ℚ) ≠ 0 by exact_mod_cast hn.ne') h

-- Two labels detect a nontrivial coset space. If the first label has several orbits,
-- distinguish one by its constant weight. If it is transitive, close the second label
-- at the base vertex by a path of weight zero along the first label.
private theorem eq_top_of_central_powers {H : Subgroup G} (hG : ¬ IsCyclic G)
    (hp : ∀ g : G, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H ∧ ∀ k : G, ⁅k, g ^ n⁆ ∈ ⁅H, H⁆) :
    H = ⊤ := by
  classical
  have hgen : Nontrivial (IsFreeGroup.Generators G) := by
    rw [← not_subsingleton_iff_nontrivial, ← FreeGroup.isCyclic_iff_subsingleton,
      (IsFreeGroup.mulEquiv G).isCyclic]
    exact hG
  obtain ⟨i, j, hij⟩ := hgen
  let x : G := generator i
  let y : G := generator j
  let O := MulAction.orbit (Subgroup.zpowers x) (base H)
  apply top_unique
  intro g _
  rw [← fixes_base_iff]
  by_contra hne
  by_cases hO : ∀ v : G ⧸ H, v ∈ O
  · let a (k : IsFreeGroup.Generators G) (v : G ⧸ H) : ℚ :=
      if k = j ∧ v = base H then 1 else 0
    have hx (v : G ⧸ H) : walkWeight a x v = 0 := by
      simp [x, walkWeight_of, a, hij]
    let U : Subgroup G :=
      { carrier := {g | ∀ v, walkWeight a g v = 0}
        one_mem' := walkWeight_one a
        mul_mem' {g h} hg hh v := by rw [walkWeight_mul, hg, hh, add_zero]
        inv_mem' {g} hg v := by rw [walkWeight_inv, hg, neg_zero] }
    obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp (hO (y • base H))
    have hzero (v : G ⧸ H) : walkWeight a (t : G)⁻¹ v = 0 :=
      U.inv_mem (Subgroup.zpowers_le.mpr (show x ∈ U from hx) t.2) v
    let r := (t : G)⁻¹ * y
    have hfix : r • base H = base H := by
      change (t : G) • base H = _ at ht
      dsimp only [r]
      rw [mul_smul, ← ht, inv_smul_smul]
    have hr (v : G ⧸ H) : walkWeight a r v = if v = base H then 1 else 0 := by
      dsimp only [r]
      rw [walkWeight_mul, hzero, zero_add]
      simp [a, y, walkWeight_of]
    have hinv (v : G ⧸ H) : walkWeight a r (r • v) = walkWeight a r v := by
      have he : r • v = base H ↔ v = base H := by
        conv_lhs => rw [← hfix]
        exact (MulAction.toPerm (β := G ⧸ H) r).injective.eq_iff (a := v) (b := base H)
      simp only [hr, he]
    have h := weight_eq_of_central_powers hp a hinv (g • base H)
    rw [hr, hr, ite_eq_right hne, ite_eq_left rfl] at h
    exact zero_ne_one h
  · push Not at hO
    obtain ⟨v, hv⟩ := hO
    let a (k : IsFreeGroup.Generators G) (w : G ⧸ H) : ℚ :=
      if k = i ∧ w ∈ O then 1 else 0
    have hx (w : G ⧸ H) : walkWeight a x w = if w ∈ O then 1 else 0 := by
      simp [x, walkWeight_of, a]
    have hinv (w : G ⧸ H) : walkWeight a x (x • w) = walkWeight a x w := by
      rw [hx, hx]
      have he : x • w ∈ O ↔ w ∈ O := by
        let t : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
        change t • w ∈ O ↔ w ∈ O
        change t • w ∈ MulAction.orbit _ _ ↔ _
        rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
        constructor
        · rintro ⟨s, hs⟩
          exact ⟨t⁻¹ * s, by rw [mul_smul, hs, inv_smul_smul]⟩
        · rintro ⟨s, hs⟩
          exact ⟨t * s, by rw [mul_smul, hs]⟩
      simp only [he]
    have h := weight_eq_of_central_powers hp a hinv v
    simp [hx, hv, O, MulAction.mem_orbit_self] at h

private theorem derived_ne_bot_of_not_cyclic (H : Subgroup G) (hH : ¬ IsCyclic H) :
    ⁅H, H⁆ ≠ ⊥ := by
  simpa [Subgroup.commutator_self_eq_bot_iff, ← IsFreeGroup.isCyclic_iff_isMulCommutative]
    using hH

omit [IsFreeGroup G] in
private theorem derived_subgroupOf {H E : Subgroup G} (h : H ≤ E) :
    ⁅H, H⁆.subgroupOf E = ⁅H.subgroupOf E, H.subgroupOf E⁆ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h,
    Subgroup.map_subgroupOf_eq_of_le (H.commutator_le_self.trans h)]

omit [IsFreeGroup G] in
private theorem commutator_mem_iff_commute {D : Subgroup G} [D.Normal] {g c : G} :
    ⁅g, c⁆ ∈ D ↔ Commute (QuotientGroup.mk' D g) (QuotientGroup.mk' D c) := by
  rw [show Commute (QuotientGroup.mk' D g) (QuotientGroup.mk' D c) ↔ _ from
    commutatorElement_eq_one_iff_mul_comm.symm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).symm

omit [IsFreeGroup G] in
private theorem central_in_sup {H K D : Subgroup G} [D.Normal] {c : G}
    (hH : ∀ g ∈ H, ⁅g, c⁆ ∈ D) (hK : ∀ g ∈ K, ⁅g, c⁆ ∈ D)
    {g : G} (hg : g ∈ H ⊔ K) : ⁅g, c⁆ ∈ D := by
  let q := QuotientGroup.mk' D
  let C := (Subgroup.centralizer {q c}).comap q
  have he (a : G) : a ∈ C ↔ ⁅a, c⁆ ∈ D := by
    change q a ∈ Subgroup.centralizer {q c} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff, commutator_mem_iff_commute]
  have hHC : H ≤ C := fun a ha ↦ (he a).2 (hH a ha)
  have hKC : K ≤ C := fun a ha ↦ (he a).2 (hK a ha)
  exact (he g).1 (sup_le hHC hKC hg)

omit [IsFreeGroup G] in
private theorem central_of_mem_both {H K : Subgroup G} [(⁅H, H⁆ : Subgroup G).Normal]
    (he : ⁅H, H⁆ = ⁅K, K⁆) (hjoin : H ⊔ K = ⊤) {c : G} (hc : c ∈ H ⊓ K)
    (g : G) : ⁅g, c⁆ ∈ ⁅H, H⁆ := by
  apply central_in_sup (H := H) (K := K)
  · exact fun a ha ↦ Subgroup.commutator_mem_commutator ha hc.1
  · rw [he]
    exact fun a ha ↦ Subgroup.commutator_mem_commutator ha hc.2
  · rw [hjoin]
    trivial

omit [IsFreeGroup G] in
private theorem join_subgroupOf_eq_top (H K : Subgroup G) :
    H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_top, Subgroup.range_subtype]

private theorem eq_top_of_common_derived {H K : Subgroup G} [(⁅H, H⁆ : Subgroup G).Normal]
    (he : ⁅H, H⁆ = ⁅K, K⁆) (hjoin : H ⊔ K = ⊤) (hG : ¬ IsCyclic G)
    {c : G} (hc : c ∈ H ⊓ K) (hcd : c ∉ ⁅H, H⁆) : H = ⊤ := by
  have hH := finiteIndex_of_central hc.1 hcd (central_of_mem_both he hjoin hc)
  have hK := finiteIndex_of_central hc.2 (he ▸ hcd)
    (he ▸ central_of_mem_both he hjoin hc)
  apply eq_top_of_central_powers hG
  intro g
  obtain ⟨n, hn, -, hg⟩ :=
    (H ⊓ K).exists_pow_mem_of_index_ne_zero (H ⊓ K).index_ne_zero g
  exact ⟨n, hn, hg.1, central_of_mem_both he hjoin hg⟩

-- Tursunbaev's intersection dichotomy for subgroups with the same normal derived subgroup.
private theorem inf_eq_derived_of_ne {D H K : Subgroup G} [D.Normal]
    (hD : D ≠ ⊥) (hH : ⁅H, H⁆ = D) (hK : ⁅K, K⁆ = D) (hne : H ≠ K) :
    H ⊓ K = D := by
  apply le_antisymm _ (le_inf (hH ▸ H.commutator_le_self) (hK ▸ K.commutator_le_self))
  intro c hc
  by_contra hcd
  let E := H ⊔ K
  let A := H.subgroupOf E
  let B := K.subgroupOf E
  have hE : D ≤ E := (hH ▸ H.commutator_le_self).trans le_sup_left
  have hA : ⁅A, A⁆ = D.subgroupOf E := (derived_subgroupOf le_sup_left).symm.trans (by rw [hH])
  have hB : ⁅B, B⁆ = D.subgroupOf E := (derived_subgroupOf le_sup_right).symm.trans (by rw [hK])
  have hfree : ¬ IsCyclic E := by
    intro hcyc
    exact hD ((Subgroup.eq_bot_iff_forall D).mpr fun d hd ↦ by
      have := hcyc
      have hsub : IsMulCommutative E := inferInstance
      have hcomm : ⁅A, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (fun a _ b _ ↦ mul_comm' b a)
      have hmem : (⟨d, hE hd⟩ : E) ∈ ⁅A, A⁆ := hA.symm ▸ hd
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem)
  let z : E := ⟨c, (show H ≤ E from le_sup_left) hc.1⟩
  have hz : z ∈ A ⊓ B := hc
  have hzd : z ∉ D.subgroupOf E := hcd
  have hAn : (⁅A, A⁆ : Subgroup E).Normal := hA.symm ▸ inferInstance
  have hBn : (⁅B, B⁆ : Subgroup E).Normal := hB.symm ▸ inferInstance
  have hj : A ⊔ B = ⊤ := join_subgroupOf_eq_top H K
  have hab := hA.trans hB.symm
  have ha := eq_top_of_common_derived hab hj hfree hz (hA.symm ▸ hzd)
  have hb := eq_top_of_common_derived hab.symm (sup_comm A B ▸ hj) hfree
    (show z ∈ B ⊓ A from ⟨hz.2, hz.1⟩) (hB.symm ▸ hzd)
  apply hne
  rw [← Subgroup.map_subgroupOf_eq_of_le (H := H) (K := E) le_sup_left,
    ← Subgroup.map_subgroupOf_eq_of_le (H := K) (K := E) le_sup_right]
  exact congrArg (Subgroup.map E.subtype) (ha.trans hb.symm)

end Comparison

section Roots

variable {G : Type} [Group G] [IsFreeGroup G]

private theorem exists_mem_not_derived (H : Subgroup G) (hH : H ≠ ⊥) :
    ∃ d ∈ H, d ∉ ⁅H, H⁆ := by
  have hn : Nonempty (IsFreeGroup.Generators H) := by
    by_contra he
    have : IsEmpty (IsFreeGroup.Generators H) := not_nonempty_iff.mp he
    have : Subsingleton H := (IsFreeGroup.mulEquiv H).symm.injective.subsingleton
    exact hH ((Subgroup.eq_bot_iff_forall H).mpr fun x hx ↦ congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : H) 1))
  obtain ⟨i⟩ := hn
  let f : H →* Multiplicative ℚ := IsFreeGroup.lift fun _ ↦ Multiplicative.ofAdd 1
  refine ⟨(generator i : H).1, (generator i : H).2, ?_⟩
  intro h
  rw [← H.map_subtype_commutator] at h
  have hh := (Subgroup.mem_map_iff_mem (x := generator i) H.subtype_injective).mp h
  have hf := Group.Abelianization.commutator_le_ker f hh
  simp only [MonoidHom.mem_ker, f, generator, IsFreeGroup.lift_of] at hf
  exact one_ne_zero (congrArg Multiplicative.toAdd hf)

-- A finite set of coset differences detects every subgroup in which d is in the derived group.
private theorem finite_derived_witness (D : Subgroup G) {d : G} (hd : d ∈ D)
    (hdd : d ∉ ⁅D, D⁆) :
    ∃ T : Set G, T.Finite ∧ (∀ t ∈ T, t ∉ D) ∧
      ∀ H : Subgroup G, D ≤ H → d ∈ ⁅H, H⁆ → ∃ t ∈ T, t ∈ H := by
  classical
  obtain ⟨a, ha⟩ := weight_detects_loop hd hdd
  obtain ⟨S, hS⟩ := finite_vertices d (base D)
  let P : Set ((G ⧸ D) × (G ⧸ D)) := {v | v.1 ∈ S ∧ v.2 ∈ S ∧ v.1 ≠ v.2}
  let diff (v : (G ⧸ D) × (G ⧸ D)) := v.1.out⁻¹ * v.2.out
  have hP : P.Finite := (S.finite_toSet.prod S.finite_toSet).subset fun _ hv ↦ ⟨hv.1, hv.2.1⟩
  refine ⟨diff '' P, hP.image _, ?_, ?_⟩
  · rintro _ ⟨⟨v, w⟩, ⟨_, _, hne⟩, rfl⟩ hh
    apply hne
    simpa only [QuotientGroup.out_eq'] using (QuotientGroup.eq (s := D)).2 hh
  · intro H hDH hdH
    by_contra! ht
    let p := Subgroup.quotientMapOfLE hDH
    have hp (g : G) (v : G ⧸ D) : p (g • v) = g • p v := by
      induction v using QuotientGroup.induction_on
      rfl
    have hi : Set.InjOn p (S : Set (G ⧸ D)) := by
      intro v hv w hw he
      by_contra hne
      have he' : (v.out : G ⧸ H) = (w.out : G ⧸ H) := by
        rw [← Subgroup.quotientMapOfLE_apply_mk hDH,
          ← Subgroup.quotientMapOfLE_apply_mk hDH, QuotientGroup.out_eq',
          QuotientGroup.out_eq']
        exact he
      exact ht (diff (v, w)) ⟨(v, w), ⟨hv, hw, hne⟩, rfl⟩ (QuotientGroup.eq.mp he')
    let b (i : IsFreeGroup.Generators G) (w : G ⧸ H) : ℚ :=
      if h : ∃ v ∈ S, p v = w then a i h.choose else 0
    have hb (i : IsFreeGroup.Generators G) (v : G ⧸ D) (hv : v ∈ S) :
        b i (p v) = a i v := by
      have h : ∃ w ∈ S, p w = p v := ⟨v, hv, rfl⟩
      dsimp only [b]
      rw [dite_eq_left h, hi h.choose_spec.1 hv h.choose_spec.2]
    have h := hS (fun i v ↦ b i (p v)) a hb
    rw [walkWeight_natural p hp] at h
    exact ha (h.symm.trans (walkWeight_zero_of_mem_derived b hdH))

private abbrev DerivedRoots (D : Subgroup G) :=
  {H : Subgroup G // ⁅H, H⁆ = D}

private theorem finite_roots (D : Subgroup G) [D.Normal] (hD : D ≠ ⊥) :
    Finite (DerivedRoots D) := by
  classical
  obtain ⟨d, hd, hd'⟩ := exists_mem_not_derived D hD
  obtain ⟨T, hT, hTD, hdetect⟩ := finite_derived_witness D hd hd'
  have witness (H : DerivedRoots D) : ∃ t ∈ T, t ∈ (H : Subgroup G) :=
    hdetect H (H.2.ge.trans H.1.commutator_le_self) (by simpa only [H.2] using hd)
  let f (H : DerivedRoots D) : T := ⟨(witness H).choose, (witness H).choose_spec.1⟩
  let := hT.to_subtype
  apply Finite.of_injective f
  intro A B he
  apply Subtype.ext
  by_contra hne
  have htA := (witness A).choose_spec.2
  have htB : (f A : G) ∈ (B : Subgroup G) :=
    (congrArg Subtype.val he).symm ▸ (witness B).choose_spec.2
  exact hTD _ (f A).2 (inf_eq_derived_of_ne hD A.2 B.2 hne ▸
    (show (f A : G) ∈ A.1 ⊓ B.1 from ⟨htA, htB⟩))

@[instance_reducible]
private def conjugationOnRoots (D : Subgroup G) [D.Normal] : MulAction G (DerivedRoots D) where
  smul g H := ⟨H.1.map (MulAut.conj g), by
    rw [← Subgroup.map_commutator, H.2, Subgroup.Normal.map_conj_eq]⟩
  one_smul H := by
    apply Subtype.ext
    change H.1.map (MulAut.conj (1 : G)).toMonoidHom = H.1
    rw [map_one]
    exact Subgroup.map_id _
  mul_smul g h H := by
    apply Subtype.ext
    change H.1.map (MulAut.conj (g * h)) =
      (H.1.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_map, map_mul]
    rfl

private theorem exists_pow_mem_normalizer {D : Subgroup G} [D.Normal] (hD : D ≠ ⊥)
    (g : G) (H : DerivedRoots D) : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ Subgroup.normalizer (H.1 : Set G) := by
  let := finite_roots D hD
  let := conjugationOnRoots D
  let f := MulAction.toPermHom G (DerivedRoots D)
  obtain ⟨n, hn, -, hgn⟩ := f.ker.exists_pow_mem_of_index_ne_zero f.ker.index_ne_zero g
  have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hgn) H
  exact ⟨n, hn, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val h)⟩

private theorem quotient_eq_of_pow_eq {D H : Subgroup G} [D.Normal] (hH : ⁅H, H⁆ = D)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) {n : ℕ} (hn : 0 < n)
    (h : (QuotientGroup.mk' D x) ^ n = (QuotientGroup.mk' D y) ^ n) :
    QuotientGroup.mk' D x = QuotientGroup.mk' D y := by
  let a : H := ⟨x, hx⟩
  let b : H := ⟨y, hy⟩
  have he (s t : H) : QuotientGroup.mk' D s = QuotientGroup.mk' D t ↔
      Group.Abelianization.of s = Group.Abelianization.of t := by
    change ((s : G) : G ⧸ D) = (t : G) ↔
      (s : H ⧸ _root_.commutator H) = t
    rw [QuotientGroup.eq, QuotientGroup.eq, ← hH, ← H.map_subtype_commutator]
    exact Subgroup.mem_map_iff_mem (x := s⁻¹ * t) H.subtype_injective
  apply (he a b).2
  apply abelian_pow_injective hn
  change Group.Abelianization.of a ^ n = Group.Abelianization.of b ^ n
  rw [← map_pow, ← map_pow, ← he]
  simpa only [Subgroup.coe_pow, map_pow] using h

private theorem pow_not_mem_derived {D H : Subgroup G} [D.Normal] (hH : ⁅H, H⁆ = D)
    {x : G} (hx : x ∈ H) (hxd : x ∉ D) {n : ℕ} (hn : 0 < n) : x ^ n ∉ D := by
  intro h
  apply hxd
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' D x = 1
  rw [← map_one (QuotientGroup.mk' D)]
  apply quotient_eq_of_pow_eq hH hx H.one_mem hn
  rw [← map_pow, map_one, one_pow]
  exact (QuotientGroup.eq_one_iff _).mpr h

end Roots

section Uniqueness

variable {G : Type} [Group G] [IsFreeGroup G]

private theorem eq_of_common_normal_derived {D H K : Subgroup G} [D.Normal]
    (hD : D ≠ ⊥) (hH : ⁅H, H⁆ = D) (hK : ⁅K, K⁆ = D) : H = K := by
  by_contra hne
  have hi := inf_eq_derived_of_ne hD hH hK hne
  have hDH : D ≤ H := hH ▸ H.commutator_le_self
  have hDK : D ≤ K := hK ▸ K.commutator_le_self
  obtain ⟨k, hk, hkD⟩ := exists_mem_not_derived K (fun h ↦ hD (le_bot_iff.mp (hDK.trans h.le)))
  rw [hK] at hkD
  obtain ⟨m, hm, hmn⟩ := exists_pow_mem_normalizer hD k ⟨H, hH⟩
  let q := k ^ m
  have hqK : q ∈ K := K.pow_mem hk _
  have hqD : q ∉ D := pow_not_mem_derived hK hk hkD hm
  let π := QuotientGroup.mk' D
  -- A power of k normalizes H. Its commutators with powers of elements of H belong
  -- to both roots, so it centralizes H modulo D by torsion-freeness of H's abelianization.
  have hq (x : G) (hx : x ∈ H) : Commute (π q) (π x) := by
    obtain ⟨n, hn, hnn⟩ := exists_pow_mem_normalizer hD x ⟨K, hK⟩
    have hnp : x ^ n ∈ H := H.pow_mem hx _
    have hnH : ⁅q, x ^ n⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp hmn _).mp hnp) (H.inv_mem hnp)
    have hnK : ⁅q, x ^ n⁆ ∈ K := by
      have he : ⁅q, x ^ n⁆ = q * (x ^ n * q⁻¹ * (x ^ n)⁻¹) :=
        by simp only [commutatorElement_def, mul_assoc]
      rw [he]
      exact K.mul_mem hqK ((Subgroup.mem_normalizer_iff.mp hnn _).mp (K.inv_mem hqK))
    have hnD : ⁅q, x ^ n⁆ ∈ D := hi ▸ (show ⁅q, x ^ n⁆ ∈ H ⊓ K from ⟨hnH, hnK⟩)
    have hcomm : Commute (π q) ((π x) ^ n) := by
      rw [← map_pow]
      exact commutator_mem_iff_commute.mp hnD
    have he : π (q * x * q⁻¹) = π x := by
      apply quotient_eq_of_pow_eq hH ((Subgroup.mem_normalizer_iff.mp hmn _).mp hx) hx hn
      have hpow : (q * x * q⁻¹) ^ n = q * x ^ n * q⁻¹ :=
        map_pow (MulAut.conj q) x n |>.symm
      rw [← map_pow, hpow]
      simp only [map_mul, map_inv, map_pow]
      change π q * (π x ^ n) * (π q)⁻¹ = π x ^ n
      rw [hcomm.eq, mul_inv_cancel_right]
    change π q * π x = π x * π q
    rw [map_mul, map_mul, map_inv] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨c, hc, hcD⟩ := exists_mem_not_derived H (fun h ↦ hD (le_bot_iff.mp (hDH.trans h.le)))
  let P := Subgroup.zpowers q
  let E := H ⊔ P
  let A := H.subgroupOf E
  have hA : ⁅A, A⁆ = D.subgroupOf E := (derived_subgroupOf le_sup_left).symm.trans (by rw [hH])
  let c' : E := ⟨c, (show H ≤ E from le_sup_left) hc⟩
  have hcent (g : E) : ⁅g, c'⁆ ∈ ⁅A, A⁆ := by
    rw [hA]
    change ⁅(g : G), c⁆ ∈ D
    apply central_in_sup (H := H) (K := P) _ _ g.2
    · exact fun x hx ↦ hH ▸ Subgroup.commutator_mem_commutator hx hc
    · intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact commutator_mem_iff_commute.mpr (by simpa only [map_zpow] using (hq c hc).zpow_left j)
  have hfinite : A.FiniteIndex := finiteIndex_of_central (show c' ∈ A from hc)
    (by rwa [hA, Subgroup.mem_subgroupOf, ← hH]) hcent
  let q' : E := ⟨q, (show P ≤ E from le_sup_right) (Subgroup.mem_zpowers q)⟩
  obtain ⟨n, hn, -, hmem⟩ := A.exists_pow_mem_of_index_ne_zero A.index_ne_zero q'
  have hnH : q ^ n ∈ H := hmem
  exact pow_not_mem_derived hK hqK hqD hn (hi ▸ (show q ^ n ∈ H ⊓ K from ⟨hnH, K.pow_mem hqK n⟩))

end Uniqueness

/--
**A non-cyclic subgroup of a free group with normal derived subgroup is normal.** Let $F$ be a
free group on an arbitrary set of generators, and suppose that $F$ is not cyclic. Then every
subgroup $R$ of $F$ that is not cyclic and whose derived subgroup $[R, R]$ is normal in $F$ is
itself normal in $F$.

Resolved true: Tursunbaev proves that subgroups $H$, $K$ of a free group of arbitrary rank whose
derived subgroups $H' = [H, H]$ and $K' = [K, K]$ are equal and nontrivial coincide; for a
non-cyclic $R$ with $R' = [R, R]$ normal in $F$ and any $f \in F$, the conjugate
$R^f = f^{-1} R f$ satisfies $(R^f)' = (R')^f = R' \ne 1$, so $R^f = R$. The Kourovka Notebook
(21st issue) marks 11.124 solved, "Yes, it is true".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.124 (V. E. Shpilrain);
resolution: A. Tursunbaev, Subgroups of free groups with the same derived subgroup, arXiv:2609.06755
(2026), main theorem (subgroups `H`, `K` of a free group of arbitrary rank with `H' = K' ≠ 1` are
equal) and its corollary answering 11.124; the Kourovka Notebook (21st issue) marks 11.124 solved,
https://arxiv.org/abs/2609.06755.
-/
public theorem derivedNormalImpliesNormal_holds : derivedNormalImpliesNormal := by
  intro α _ R hR hnormal
  have hD := derived_ne_bot_of_not_cyclic R hR
  apply Subgroup.normal_iff_map_conj_eq.mpr
  intro g
  apply eq_of_common_normal_derived hD _ rfl
  rw [← Subgroup.map_commutator, Subgroup.Normal.map_conj_eq]


end

end MathlibExt.GroupTheory.FreeGroupDerivedNormalSubgroupKourovka11Problem124Wanted
