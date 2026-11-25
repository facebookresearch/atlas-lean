/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group

/-!
# Just finite presentations of finite groups (Kourovka Notebook Problem 21.10)

Kourovka Notebook, Problem 21.10 (Y. Barnea), marked solved in the 21st issue: we call a group
presentation finite if it represents a finite group. We say that a presentation is just finite if it
is finite and is no longer finite on removal of any relation from it. Is it true that every finite
group has a just finite presentation?

We prove that every finite group admits a just finite presentation.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.10 (Y. Barnea). UnsolvedMath record
UM-00002519 (`KOU-21.10`), dataset ulamai/UnsolvedMath v1.8.0.

Presentations have finitely many generators `Fin n` and a finite set `R` of relators, as in the
resolving paper ("a finite presentation"); removing `r` gives `PresentedGroup (R.erase r)`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10Wanted

/-- **Barnea's question on just finite presentations (Kourovka 21.10).** The statement that every
finite group $G$ has a just finite presentation: a presentation $\langle X \mid R \rangle$ with $X$
and $R$ finite that defines $G$ and such that removing any single relator from $R$ gives a
presentation of an infinite group. -/
def finiteGroupHasJustFinitePresentation : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃* G) ∧
    ∀ r ∈ R, Infinite (PresentedGroup ((R.erase r : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))))

open Subgroup
open Monoid.PushoutI

section

variable {α G H : Type} [Group G] [Group H]

-- The two conjugation equations give opposite expressions for the same commutator.
private theorem conjugates_square_eq_one {u v : H}
    (huv : u⁻¹ * v * u = v ^ 2) (hvu : v⁻¹ * u * v = u ^ 2) :
    u = 1 ∧ v = 1 := by
  have hinv : u⁻¹ * v⁻¹ * u = (v ^ 2)⁻¹ := by
    rw [← huv]
    group
  have h : u = v⁻¹ := calc
    u = u⁻¹ * (u ^ 2) := by group
    _ = u⁻¹ * v⁻¹ * u * v := by rw [← hvu]; group
    _ = v⁻¹ := by rw [hinv]; group
  have hv : v = 1 := by
    rw [h] at huv
    have heq : v = v ^ 2 := by
      calc
        v = (v⁻¹)⁻¹ * v * v⁻¹ := by group
        _ = v ^ 2 := huv
    exact mul_left_cancel (show v * v = v * 1 by simpa [pow_two] using heq.symm)
  exact ⟨by simp [h, hv], hv⟩

private def conjugationRelator (u v : H) : H := u⁻¹ * v * u * (v ^ 2)⁻¹

private theorem conjugationRelator_eq_one {u v : H} :
    conjugationRelator u v = 1 ↔ u⁻¹ * v * u = v ^ 2 :=
  mul_inv_eq_one

private theorem map_conjugationRelator (f : G →* H) (u v : G) :
    f (conjugationRelator u v) = conjugationRelator (f u) (f v) := by
  simp [conjugationRelator]

private abbrev EnlargedGenerators (R : Finset (FreeGroup α)) := α ⊕ ↥R

private def replacement (R : Finset (FreeGroup α)) (i : R) (reverse : Bool) :
    FreeGroup (EnlargedGenerators R) :=
  let u := FreeGroup.map Sum.inl i.val
  let v := FreeGroup.of (Sum.inr i)
  if reverse then conjugationRelator v u else conjugationRelator u v

private noncomputable def replacements (R : Finset (FreeGroup α)) :
    Finset (FreeGroup (EnlargedGenerators R)) := by
  classical
  exact Finset.univ.image fun p : R × Bool => replacement R p.1 p.2

private theorem mem_replacements_iff (R : Finset (FreeGroup α))
    (w : FreeGroup (EnlargedGenerators R)) :
    w ∈ replacements R ↔ ∃ (i : R) (reverse : Bool), replacement R i reverse = w := by
  classical
  simp [replacements]

private theorem mem_replacements (R : Finset (FreeGroup α)) (i : R) (reverse : Bool) :
    replacement R i reverse ∈ replacements R :=
  (mem_replacements_iff R _).mpr ⟨i, reverse, rfl⟩

private def extend (R : Finset (FreeGroup α)) (f : FreeGroup α →* H) (b : R → H) :
    FreeGroup (EnlargedGenerators R) →* H :=
  FreeGroup.lift (Sum.elim (f ∘ FreeGroup.of) b)

private theorem extend_map_inl (R : Finset (FreeGroup α)) (f : FreeGroup α →* H) (b : R → H)
    (w : FreeGroup α) : extend R f b (FreeGroup.map Sum.inl w) = f w := by
  have h : (extend R f b).comp (FreeGroup.map Sum.inl) = f := by
    apply FreeGroup.ext_hom
    intro x
    simp [extend, FreeGroup.map.of]
  exact DFunLike.congr_fun h w

private theorem extend_replacement (R : Finset (FreeGroup α)) (f : FreeGroup α →* H)
    (b : R → H) (i : R) (reverse : Bool) :
    extend R f b (replacement R i reverse) =
      if reverse then conjugationRelator (b i) (f i.val)
      else conjugationRelator (f i.val) (b i) := by
  cases reverse <;>
    simp [replacement, map_conjugationRelator, extend_map_inl, show
      extend R f b (FreeGroup.of (Sum.inr i)) = b i by simp [extend]]

private def descend {S : Set (FreeGroup α)} (f : FreeGroup α →* H)
    (hf : ∀ w ∈ S, f w = 1) : PresentedGroup S →* H :=
  QuotientGroup.lift (normalClosure S) f
    (normalClosure_le_normal fun w hw => f.mem_ker.mpr (hf w hw))

private theorem descend_mk {S : Set (FreeGroup α)} (f : FreeGroup α →* H)
    (hf : ∀ w ∈ S, f w = 1) (w : FreeGroup α) :
    descend f hf (PresentedGroup.mk S w) = f w := rfl

private noncomputable def replacementEquiv (R : Finset (FreeGroup α)) :
    PresentedGroup (replacements R : Set (FreeGroup (EnlargedGenerators R))) ≃*
      PresentedGroup (R : Set (FreeGroup α)) := by
  let q := PresentedGroup.mk (R : Set (FreeGroup α))
  let p := PresentedGroup.mk (replacements R : Set (FreeGroup (EnlargedGenerators R)))
  have hrelations (i : R) : p (FreeGroup.map Sum.inl i.val) = 1 ∧
      p (FreeGroup.of (Sum.inr i)) = 1 := by
    apply conjugates_square_eq_one
    · apply conjugationRelator_eq_one.mp
      rw [← map_conjugationRelator]
      exact PresentedGroup.one_of_mem (mem_replacements R i false)
    · apply conjugationRelator_eq_one.mp
      rw [← map_conjugationRelator]
      exact PresentedGroup.one_of_mem (mem_replacements R i true)
  let f := descend (S := (replacements R : Set (FreeGroup (EnlargedGenerators R))))
    (extend R q (fun _ => 1)) (by
    intro w hw
    obtain ⟨i, rev, rfl⟩ := (mem_replacements_iff R w).mp hw
    have hi : q i.val = 1 := PresentedGroup.one_of_mem i.property
    simp [extend_replacement, hi, conjugationRelator])
  let g := descend (S := (R : Set (FreeGroup α))) (p.comp (FreeGroup.map Sum.inl))
    (fun w hw => (hrelations ⟨w, hw⟩).1)
  have hfg : f.comp g = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro x
    change f (g (q (FreeGroup.of x))) = q (FreeGroup.of x)
    rw [show g (q (FreeGroup.of x)) = p (FreeGroup.map Sum.inl (FreeGroup.of x)) from rfl]
    exact extend_map_inl R q (fun _ => 1) (FreeGroup.of x)
  have hgf : g.comp f = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro x
    change g (f (p (FreeGroup.of x))) = p (FreeGroup.of x)
    cases x with
    | inl a =>
      rw [show f (p (FreeGroup.of (Sum.inl a))) = q (FreeGroup.of a) by
        exact FreeGroup.lift_apply_of]
      change p (FreeGroup.map Sum.inl (FreeGroup.of a)) = _
      rw [FreeGroup.map.of]
    | inr i =>
      rw [show f (p (FreeGroup.of (Sum.inr i))) = 1 by exact FreeGroup.lift_apply_of, map_one]
      exact (hrelations i).2.symm
  exact { f with
    invFun := g
    left_inv := DFunLike.congr_fun hgf
    right_inv := DFunLike.congr_fun hfg }

-- Each new generator is assigned the identity except the one for the deleted pair.
private noncomputable def deletionMap [DecidableEq α] (R : Finset (FreeGroup α)) (i : R)
    (rev : Bool) (f : FreeGroup α →* H) (b : H) (hf : ∀ j : R, j ≠ i → f j.val = 1)
    (hb : (if rev then conjugationRelator (f i.val) b else conjugationRelator b (f i.val)) = 1) :
    PresentedGroup ((replacements R).erase (replacement R i rev) :
      Set (FreeGroup (EnlargedGenerators R))) →* H := by
  apply descend (extend R f fun j => if j = i then b else 1)
  intro w hw
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
  obtain ⟨j, dir, rfl⟩ := (mem_replacements_iff R w).mp hmem
  rw [extend_replacement]
  by_cases hji : j = i
  · subst j
    cases rev <;> cases dir
    · exact (hne rfl).elim
    · simpa using hb
    · simpa using hb
    · exact (hne rfl).elim
  · simp [hji, hf j hji, conjugationRelator]

private theorem deletionMap_old [DecidableEq α] (R : Finset (FreeGroup α)) (i : R) (rev : Bool)
    (f : FreeGroup α →* H) (b : H) (hf) (hb) (w : FreeGroup α) :
    deletionMap R i rev f b hf hb (PresentedGroup.mk _ (FreeGroup.map Sum.inl w)) = f w :=
  extend_map_inl R f _ w

private theorem deletionMap_new [DecidableEq α] (R : Finset (FreeGroup α)) (i : R) (rev : Bool)
    (f : FreeGroup α →* H) (b : H) (hf) (hb) :
    deletionMap R i rev f b hf hb (PresentedGroup.of (Sum.inr i)) = b := by
  simp [deletionMap, PresentedGroup.of, descend_mk, extend]

private theorem exists_irredundant [Finite G] : ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃* G) ∧
      ∀ i : R, PresentedGroup.mk (R.erase i.val : Set (FreeGroup (Fin n))) i.val ≠ 1 := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
  obtain ⟨R, hR, hminimal⟩ := exists_minimalFor_of_wellFoundedLT
    (fun R : Finset (FreeGroup (Fin n)) =>
      Nonempty (PresentedGroup (R : Set (FreeGroup (Fin n))) ≃* G))
    Finset.card ⟨hS.toFinset, by
      rw [hS.coe_toFinset]
      exact ⟨e.symm⟩⟩
  refine ⟨n, R, hR, fun i hi => ?_⟩
  have heq : normalClosure (R.erase i.val : Set (FreeGroup (Fin n))) =
      normalClosure (R : Set (FreeGroup (Fin n))) := by
    apply le_antisymm (normalClosure_mono (Finset.erase_subset _ _))
    apply normalClosure_le_normal
    intro w hw
    by_cases hwi : w = i.val
    · subst w
      exact PresentedGroup.mk_eq_one_iff.mp hi
    · exact subset_normalClosure (Finset.mem_erase.mpr ⟨hwi, hw⟩)
  obtain ⟨eR⟩ := hR
  have hdel : Nonempty (PresentedGroup (R.erase i.val : Set (FreeGroup (Fin n))) ≃* G) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans eR⟩
  have hlt := Finset.card_erase_lt_of_mem i.property
  exact hlt.not_ge (hminimal hdel hlt.le)

private theorem cyclic_presentation [Finite G] [IsCyclic G] :
    ∃ R : Finset (FreeGroup (Fin 1)), Nonempty (PresentedGroup (R : Set (FreeGroup (Fin 1))) ≃* G) ∧
      ∀ r ∈ R, Infinite (PresentedGroup (R.erase r : Set (FreeGroup (Fin 1)))) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let e : FreeGroup (Fin 1) ≃* Multiplicative ℤ := FreeGroup.mulEquivIntOfUnique
  let f := (zpowersHom G g).comp e.toMonoidHom
  let r := e.symm (Multiplicative.ofAdd (orderOf g : ℤ))
  have hker : normalClosure ({r} : Set (FreeGroup (Fin 1))) = f.ker := by
    have hmem : r ∈ f.ker := by
      change zpowersHom G g (e r) = 1
      simp [r, zpowersHom_apply, pow_orderOf_eq_one]
    apply le_antisymm (normalClosure_le_normal (Set.singleton_subset_iff.mpr hmem))
    intro w hw
    have hw' : e w ∈ (zpowersHom G g).ker := hw
    rw [zpowersHom_ker_eq] at hw'
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw'
    have hrw : r ^ k = w := e.injective (by simpa [r] using hk)
    rw [← hrw]
    exact zpow_mem (subset_normalClosure (Set.mem_singleton r)) k
  have hf : Function.Surjective f :=
    (MonoidHom.range_eq_top.mp ((range_zpowersHom g).trans hg)).comp e.surjective
  refine ⟨{r}, ⟨?_⟩, ?_⟩
  · rw [Finset.coe_singleton]
    exact (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  · intro w hw
    have he : w = r := Finset.mem_singleton.mp hw
    subst w
    have hemp : ({r} : Finset _).erase r = ∅ := Finset.erase_singleton _
    rw [hemp, Finset.coe_empty]
    let eb : PresentedGroup (∅ : Set (FreeGroup (Fin 1))) ≃* FreeGroup (Fin 1) :=
      (QuotientGroup.quotientMulEquivOfEq Subgroup.normalClosure_empty).trans
        QuotientGroup.quotientBot
    let : Infinite (FreeGroup (Fin 1)) := Infinite.of_injective e.symm e.symm.injective
    exact Infinite.of_injective eb.symm eb.symm.injective

-- An alternating product of letters outside the amalgamated subgroup has infinite order.
private theorem alternating_infinite_order {ι C : Type} {A : ι → Type}
    [Group C] [∀ i, Group (A i)] (φ : ∀ i, C →* A i)
    (hφ : ∀ i, Function.Injective (φ i)) {i j : ι} (hij : i ≠ j)
    (a : A i) (b : A j) (ha : a ∉ (φ i).range) (hb : b ∉ (φ j).range) :
    ¬ IsOfFinOrder (of (φ := φ) i a * of j b) := by
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  let words : ℕ → {w : NormalWord d // w.fstIdx ≠ some j} :=
    Nat.rec ⟨NormalWord.empty, by simp [Monoid.CoprodI.Word.fstIdx]⟩ fun _ w =>
      let tail := NormalWord.cons b w.val w.property hb
      ⟨NormalWord.cons a tail (by simp [tail, Monoid.CoprodI.Word.fstIdx, Ne.symm hij]) ha,
        by simp [Monoid.CoprodI.Word.fstIdx, hij]⟩
  have hprod (n : ℕ) : (words n).val.prod = (of i a * of j b) ^ n := by
    induction n with
    | zero => simp [words]
    | succ n ih => simp [words, ih, pow_succ', mul_assoc]
  have hlen (n : ℕ) : (words n).val.toList.length = 2 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [words, ih, Nat.mul_succ, Nat.add_assoc]
  apply not_isOfFinOrder_of_injective_pow
  intro n m hnm
  have hw : (words n).val = (words m).val :=
    NormalWord.prod_injective ((hprod n).trans (hnm.trans (hprod m).symm))
  have h := congrArg (fun w : NormalWord d => w.toList.length) hw
  rw [hlen, hlen] at h
  omega

private abbrev TwoFactors (H B : Type) : Bool → Type := Bool.rec H B

private abbrev twoGroups (H B : Type) [Group H] [Group B] (j : Bool) : Group (TwoFactors H B j) :=
  Bool.rec (motive := fun i => Group (TwoFactors H B i)) inferInstance inferInstance j

-- A cyclic action by doubling supplies the second factor of the amalgamated product.
private theorem finite_conjugation_model [Finite H] (r : H) (hr : r ≠ 1)
    (hH : ¬ IsCyclic H) :
    ∃ (K : Type) (_ : Group K) (f : H →* K) (b : K),
      f r⁻¹ * b * f r = b ^ 2 ∧ ∃ a : H, ¬ IsOfFinOrder (f a * b) := by
  let k := orderOf r
  have hk : 0 < k := orderOf_pos r
  have hk' : 1 < k := by
    have hne : k ≠ 1 := mt orderOf_eq_one_iff.mp hr
    omega
  let m := 2 ^ k - 1
  have hm : 1 < m := by
    have : 2 ^ 1 < 2 ^ k := Nat.pow_lt_pow_right (by decide) hk'
    omega
  let : Fact (1 < m) := ⟨hm⟩
  have htwo : (2 : ZMod m) ^ k = 1 := by
    have h : 2 ^ k = m + 1 := by
      have := Nat.two_pow_pos k
      omega
    exact_mod_cast (show ((2 ^ k : ℕ) : ZMod m) = 1 by rw [h, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add])
  let d : (ZMod m)ˣ := Units.ofPowEqOne 2 k htwo hk.ne'
  let c : zpowers r := ⟨r, mem_zpowers r⟩
  let powers : Multiplicative ℤ →* zpowers r := (zpowersHom H r).rangeRestrict
  let units := zpowersHom (ZMod m)ˣ d⁻¹
  have hker : powers.ker ≤ units.ker := by
    rw [show powers.ker = (zpowersHom H r).ker from MonoidHom.ker_rangeRestrict _,
      zpowersHom_ker_eq, zpowers_le]
    change d⁻¹ ^ ((k : ℕ) : ℤ) = 1
    rw [zpow_natCast, inv_pow, Units.pow_ofPowEqOne, inv_one]
  let ρ := powers.liftOfSurjective (MonoidHom.rangeRestrict_surjective _) ⟨units, hker⟩
  have hρ : ρ c = d⁻¹ := by
    have hc : powers (Multiplicative.ofAdd 1) = c := by
      apply Subtype.ext
      exact zpow_one r
    rw [← hc]
    simp [ρ, units, zpowersHom_apply]
  let action : (ZMod m)ˣ →* MulAut (Multiplicative (ZMod m)) :=
    (MulAutMultiplicative (ZMod m)).symm.toMonoidHom.comp AddAut.mulLeft
  let φ := action.comp ρ
  let B := Multiplicative (ZMod m) ⋊[φ] ↥(zpowers r)
  let t : Multiplicative (ZMod m) := Multiplicative.ofAdd 1
  let y : B := SemidirectProduct.inl t
  have hy : (SemidirectProduct.inr c : B)⁻¹ * y * SemidirectProduct.inr c = y ^ 2 := by
    rw [← map_inv, ← SemidirectProduct.inl_aut_inv, ← map_pow]
    congr 1
    have hc : (φ c)⁻¹ = action d := by
      change (action (ρ c))⁻¹ = action d
      rw [hρ, map_inv, inv_inv]
    rw [hc, pow_two]
    change Multiplicative.ofAdd ((d : ZMod m) * 1) = Multiplicative.ofAdd (1 + 1)
    rw [mul_one]
    exact congrArg Multiplicative.ofAdd one_add_one_eq_two.symm
  have hy' : y ∉ (SemidirectProduct.inr : zpowers r →* B).range := by
    rintro ⟨z, hz⟩
    have h := congrArg (fun x : B => x.left.toAdd) hz
    exact zero_ne_one h
  obtain ⟨a, ha⟩ : ∃ a, a ∉ zpowers r := by
    by_contra! hall
    exact hH (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨r, eq_top_iff.mpr fun a _ => hall a⟩)
  let groupAt : ∀ j, Group (TwoFactors H B j) := twoGroups H B
  let ψ (j : Bool) : zpowers r →* TwoFactors H B j :=
    Bool.rec (motive := fun i => zpowers r →* TwoFactors H B i)
      (zpowers r).subtype SemidirectProduct.inr j
  have hψ (j : Bool) : Function.Injective (ψ j) := by
    cases j
    · exact Subtype.val_injective
    · exact SemidirectProduct.inr_injective
  have hr' : of (φ := ψ) false r = of true (SemidirectProduct.inr c : B) :=
    (of_apply_eq_base ψ false c).trans (of_apply_eq_base ψ true c).symm
  refine ⟨Monoid.PushoutI ψ, inferInstance, of (φ := ψ) false, of true y, ?_, a, ?_⟩
  · rw [map_inv, hr', ← map_inv, ← map_mul, ← map_mul, hy, map_pow]
  · exact alternating_infinite_order ψ hψ (by decide : false ≠ true) a y
      (by simpa [ψ, Subgroup.range_subtype] using ha) hy'

private theorem replacement_erase_infinite {n : ℕ} (R : Finset (FreeGroup (Fin n)))
    (i : R) (rev : Bool)
    (hi : PresentedGroup.mk (R.erase i.val : Set (FreeGroup (Fin n))) i.val ≠ 1)
    (hnc : ¬ IsCyclic (PresentedGroup (R : Set (FreeGroup (Fin n))))) :
    Infinite (PresentedGroup ((replacements R).erase (replacement R i rev) :
      Set (FreeGroup (EnlargedGenerators R)))) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  cases rev
  · let t := Multiplicative.ofAdd (1 : ℤ)
    let f : FreeGroup (Fin n) →* Multiplicative ℤ := 1
    have hb : conjugationRelator t (f i.val) = 1 := by simp [f, conjugationRelator]
    let map := deletionMap R i false f t (by simp [f]) hb
    have ht : map (PresentedGroup.of (Sum.inr i)) = t := deletionMap_new R i false f t _ _
    have ho := map.isOfFinOrder (isOfFinOrder_of_finite (PresentedGroup.of (Sum.inr i)))
    exact (not_isOfFinOrder_of_isMulTorsionFree (show t ≠ 1 by decide)) (ht ▸ ho)
  · let S : Set (FreeGroup (Fin n)) := ↑(R.erase i.val)
    let q := PresentedGroup.mk S
    have hq (j : R) (hji : j ≠ i) : q j.val = 1 :=
      PresentedGroup.one_of_mem (Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.property⟩)
    have hb : conjugationRelator (q i.val) 1 = 1 := by simp [conjugationRelator]
    let retraction := deletionMap R i true q 1 hq hb
    have hs : Function.Surjective retraction := by
      intro x
      obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective S x
      exact ⟨PresentedGroup.mk _ (FreeGroup.map Sum.inl w), deletionMap_old R i true q 1 hq hb w⟩
    let : Finite (PresentedGroup S) := Finite.of_surjective retraction hs
    have hnc' : ¬ IsCyclic (PresentedGroup S) := by
      have hsub : S ⊆ (R : Set (FreeGroup (Fin n))) := Finset.erase_subset _ _
      let p := PresentedGroup.map (MonoidHom.id _) (fun _ hw => hsub hw)
      have hp : Function.Surjective p := by
        intro x
        obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
        exact ⟨q w, rfl⟩
      intro h
      exact hnc (isCyclic_of_surjective p hp)
    obtain ⟨K, _, f, b, hrel, a, ha⟩ := finite_conjugation_model (q i.val) hi hnc'
    have hf (j : R) (hji : j ≠ i) : (f.comp q) j.val = 1 := by simp [hq j hji]
    have hrel' : conjugationRelator ((f.comp q) i.val) b = 1 :=
      conjugationRelator_eq_one.mpr (by simpa only [map_inv, MonoidHom.comp_apply] using hrel)
    let map := deletionMap R i true (f.comp q) b hf hrel'
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective S a
    have hm := deletionMap_old R i true (f.comp q) b hf hrel' w
    have hmb := deletionMap_new R i true (f.comp q) b hf hrel'
    let x : PresentedGroup ((replacements R).erase (replacement R i true) :
        Set (FreeGroup (EnlargedGenerators R))) :=
      PresentedGroup.mk _ (FreeGroup.map Sum.inl w) * PresentedGroup.of (Sum.inr i)
    have heq : map x = f a * b := by
      change map (_ * _) = _
      rw [map_mul, hm, hmb, MonoidHom.comp_apply, hw]
    exact ha (heq ▸ map.isOfFinOrder (isOfFinOrder_of_finite x))

end

/--
**Every finite group has a just finite presentation.** For every finite group $G$ there are a
natural number $n$ and a finite subset $R$ of the free group on $n$ generators $x_1, \dots, x_n$
such that the group $\langle x_1, \dots, x_n \mid R \rangle$ is isomorphic to $G$ and, for every
$r \in R$, the group $\langle x_1, \dots, x_n \mid R \setminus \{r\} \rangle$ is infinite. That is,
the answer to Kourovka Problem 21.10 is positive.

Lackenby's paper acknowledges assistance from the Google DeepMind AI co-mathematician tool.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.10 (Y. Barnea);
resolution: M. Lackenby, Every finite group admits a just finite presentation, preprint,
arXiv:2605.10402 (2026), Theorem 1: every finite group admits a finite, just finite presentation (a
consequence of Theorem 2 on just-(FA) presentations); Kourovka Notebook (21st issue), Problem 21.10:
Yes, it is true, https://arxiv.org/abs/2605.10402.
-/
public theorem finiteGroupHasJustFinitePresentation_holds :
    finiteGroupHasJustFinitePresentation := by
  intro G _ _
  by_cases hG : IsCyclic G
  · obtain ⟨R, hR⟩ := cyclic_presentation (G := G)
    exact ⟨1, R, hR⟩
  obtain ⟨n, R, ⟨e⟩, hir⟩ := exists_irredundant (G := G)
  have hnc : ¬ IsCyclic (PresentedGroup (R : Set (FreeGroup (Fin n)))) := by
    intro h
    exact hG (isCyclic_of_surjective e.toMonoidHom e.surjective)
  let T := replacements R
  let E := Fintype.equivFin (EnlargedGenerators R)
  let F := FreeGroup.freeGroupCongr E
  refine ⟨_, T.image F, ?_, ?_⟩
  · refine ⟨?_⟩
    have he := PresentedGroup.equivPresentedGroup (T : Set (FreeGroup (EnlargedGenerators R))) E
    have he' := he.symm.trans ((replacementEquiv R).trans e)
    rw [Finset.coe_image]
    exact he'
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i, rev, rfl⟩ := (mem_replacements_iff R w).mp hw
    rw [← Finset.image_erase F.injective, Finset.coe_image]
    let := replacement_erase_infinite R i rev (hir i) hnc
    exact Infinite.of_injective _ (PresentedGroup.equivPresentedGroup _ E).injective

end MathlibExt.GroupTheory.JustFinitePresentationKourovka21Problem10Wanted
