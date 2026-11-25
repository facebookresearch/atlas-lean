/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.MonoidAlgebra.Defs

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Kapranov's theorem for tropical hypersurfaces

This module proves that the tropical hypersurface of a nonzero Laurent polynomial equals the
closure of the coordinatewise valuations of its torus zeros over an algebraically closed,
nontrivially valued field. It also defines tropicalization and coordinatewise valuations for ideals.

For a weight in the value group, rescale the coordinates and restrict to a monomial curve
that separates the exponents. The resulting one-variable polynomial has two coefficients
of minimum valuation, so its factorization gives a root of valuation zero. To approximate
arbitrary real weights while preserving ties, use rational-linear maps into the value group
that fix all coefficient valuations and converge pointwise to the identity.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.AlgebraicGeometry.TropicalVarietyWanted

variable {K : Type*} [Field K] {n : ℕ}

/-- **Laurent polynomials.** The ring `K[x₁^{±1}, …, x_n^{±1}]`, as the monoid algebra of `ℤⁿ`. -/
abbrev LaurentPoly (K : Type*) [Field K] (n : ℕ) : Type _ :=
  AddMonoidAlgebra K (Fin n → ℤ)

/-- **Value of one term of a tropical polynomial.** For a Laurent polynomial `f = ∑ c_u x^u`, the
tropical term `val(c_u) + u · w ∈ ℝ ∪ {∞}` at the point `w ∈ ℝⁿ` (Maclagan–Sturmfels, draft
2009, Section 3.1). -/
def tropTerm (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) (w : Fin n → ℝ)
    (u : Fin n → ℤ) : WithTop ℝ :=
  v (f.coeff u) + ((∑ i, (u i : ℝ) * w i : ℝ) : WithTop ℝ)

/-- **Tropical hypersurface.** The set of `w ∈ ℝⁿ` at which the minimum
`trop(f)(w) = min_{u : c_u ≠ 0} (val(c_u) + u · w)` is attained at least twice
(Maclagan–Sturmfels, draft 2009, Definition 3.1.1). -/
def tropicalHypersurface (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) :
    Set (Fin n → ℝ) :=
  {w | ∃ u ∈ f.coeff.support, ∃ u' ∈ f.coeff.support, u ≠ u' ∧
    tropTerm v f w u = tropTerm v f w u' ∧
    ∀ u'' ∈ f.coeff.support, tropTerm v f w u ≤ tropTerm v f w u''}

/-- **Evaluation of a Laurent polynomial on the torus.** `f(y) = ∑_u c_u ∏_i y_i^{u_i}` for
`y ∈ (K^*)ⁿ`. -/
def evalTorus (f : LaurentPoly K n) (y : Fin n → Kˣ) : K :=
  f.coeff.sum fun u c ↦ c * ((∏ i, y i ^ u i : Kˣ) : K)

/-- **Coordinatewise valuations of a hypersurface.** The set
`{(val(y_1), …, val(y_n)) : y ∈ (K^*)ⁿ, f(y) = 0} ⊆ ℝⁿ` (Maclagan–Sturmfels, draft 2009,
Theorem 3.1.3, set 3, before taking the closure). -/
def valuationsOfZeros (v : AddValuation K (WithTop ℝ)) (f : LaurentPoly K n) :
    Set (Fin n → ℝ) :=
  {w | ∃ y : Fin n → Kˣ, evalTorus f y = 0 ∧ ∀ i, v (y i : K) = (w i : WithTop ℝ)}

/-- **Tropicalization of a subvariety of the torus.** For an ideal `I` of Laurent polynomials
with variety `X = V(I) ⊆ (K^*)ⁿ`, the intersection `trop(X) = ⋂_{f ∈ I} trop(V(f))` of the
tropical hypersurfaces of the polynomials in `I` (Maclagan–Sturmfels, draft 2009,
Definition 3.2.1, equation (3.1)). The zero polynomial is left out of the intersection: its
tropical hypersurface is empty under Definition 3.1.1, and excluding it makes the zero ideal
tropicalize to `ℝⁿ`, as Theorem 3.2.4 requires; the source says nothing about `f = 0`. -/
def tropicalVariety (v : AddValuation K (WithTop ℝ)) (I : Ideal (LaurentPoly K n)) :
    Set (Fin n → ℝ) :=
  ⋂ f ∈ I, ⋂ (_ : f ≠ 0), tropicalHypersurface v f

/-- **Coordinatewise valuations of a variety.** The set
`val(X) = {(val(y_1), …, val(y_n)) : y ∈ X}` for `X = V(I) ⊆ (K^*)ⁿ` (Maclagan–Sturmfels, draft
2009, Theorem 3.2.4, set 3, before taking the closure). -/
def valuationsOfVariety (v : AddValuation K (WithTop ℝ)) (I : Ideal (LaurentPoly K n)) :
    Set (Fin n → ℝ) :=
  {w | ∃ y : Fin n → Kˣ, (∀ f ∈ I, evalTorus f y = 0) ∧ ∀ i, v (y i : K) = (w i : WithTop ℝ)}

open scoped BigOperators
open Filter Topology Polynomial
variable (v : AddValuation K (WithTop ℝ))

private def unitVal : Kˣ →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd ((v (a : K)).untop ((v.ne_top_iff).2 a.ne_zero))
  map_one' := by simp
  map_mul' a b := by
    change (v ((a * b : Kˣ) : K)).untop _ = _ + _
    apply WithTop.coe_injective
    simp [WithTop.coe_add]

private lemma coe_unitVal (a : Kˣ) :
    ((unitVal v a).toAdd : WithTop ℝ) = v (a : K) :=
  WithTop.coe_untop ..

private def charVal (y : Fin n → Kˣ) (u : Fin n → ℤ) : Kˣ := ∏ i, y i ^ u i

private lemma charVal_val (y : Fin n → Kˣ) (u : Fin n → ℤ) :
    (unitVal v (charVal y u)).toAdd = ∑ i, (u i : ℝ) * (unitVal v (y i)).toAdd := by
  simp [charVal, map_prod, map_zpow, zsmul_eq_mul]

private def weight (f : LaurentPoly K n) (u : Fin n → ℤ) (w : Fin n → ℝ) : ℝ :=
  (v (f.coeff u)).untopD 0 + ∑ i, (u i : ℝ) * w i

private lemma coe_weight (f : LaurentPoly K n) {u : Fin n → ℤ} (hu : u ∈ f.coeff.support)
    (w : Fin n → ℝ) : (weight v f u w : WithTop ℝ) = tropTerm v f w u := by
  have h := v.ne_top_iff.mpr (Finsupp.mem_support_iff.mp hu)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
  simp [weight, tropTerm, ← hr, WithTop.coe_add]

private lemma continuous_weight (f : LaurentPoly K n) (u : Fin n → ℤ) :
    Continuous (weight v f u) := by
  unfold weight
  fun_prop

private lemma hypersurface_closed (f : LaurentPoly K n) : IsClosed (tropicalHypersurface v f) := by
  classical
  let S := f.coeff.support
  have heq : tropicalHypersurface v f =
      ⋃ a : S, ⋃ b : S, {w | a ≠ b} ∩ {w | weight v f a w = weight v f b w} ∩
        ⋂ c : S, {w | weight v f a w ≤ weight v f c w} := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, b, hb, hab, he, hm⟩
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨fun e ↦ hab (congrArg Subtype.val e), ?_⟩, ?_⟩
      · exact WithTop.coe_injective
          ((coe_weight v f ha w).trans (he.trans (coe_weight v f hb w).symm))
      · intro c
        exact WithTop.coe_le_coe.mp (by
          simpa only [coe_weight v f ha, coe_weight v f c.2] using hm c c.2)
    · rintro ⟨a, b, ⟨hab, he⟩, hm⟩
      refine ⟨a, a.2, b, b.2, fun h ↦ hab (Subtype.ext h), ?_, ?_⟩
      · rw [← coe_weight v f a.2, ← coe_weight v f b.2, he]
      · intro c hc
        rw [← coe_weight v f a.2, ← coe_weight v f hc]
        exact WithTop.coe_le_coe.mpr (hm ⟨c, hc⟩)
  rw [heq]
  exact isClosed_iUnion_of_finite fun a ↦ isClosed_iUnion_of_finite fun b ↦
    ((isClosed_const).inter (isClosed_eq (continuous_weight ..) (continuous_weight ..))).inter
      (isClosed_iInter fun c ↦ isClosed_le (continuous_weight ..) (continuous_weight ..))

private lemma valuationsOfZeros_subset (f : LaurentPoly K n) (hf : f ≠ 0) :
    valuationsOfZeros v f ⊆ tropicalHypersurface v f := by
  classical
  rintro w ⟨y, hy, hw⟩
  let g := fun u ↦ f.coeff u * (charVal y u : K)
  have hval (u) : v (g u) = tropTerm v f w u := by
    have hwi i : (unitVal v (y i)).toAdd = w i :=
      WithTop.coe_injective ((coe_unitVal v _).trans (hw i))
    simp only [g, v.map_mul, ← coe_unitVal, charVal_val, hwi, tropTerm]
  have hne : f.coeff ≠ 0 := fun h ↦ hf (AddMonoidAlgebra.coeff_injective h)
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image f.coeff.support (fun u ↦ v (g u))
    (Finsupp.support_nonempty_iff.mpr hne)
  by_contra h
  have hs : ∀ i ∈ f.coeff.support \ {a}, (v.toValuation) (g i) < (v.toValuation) (g a) := by
    intro i hi
    obtain ⟨hi, hia⟩ := Finset.mem_sdiff.mp hi
    change v (g a) < v (g i)
    refine (hmin i hi).lt_of_ne fun he ↦ h ⟨a, ha, i, hi, ?_, ?_, ?_⟩
    · exact (show i ≠ a by simpa using hia).symm
    · simpa only [← hval] using he
    · simpa only [← hval] using hmin
  have he := v.toValuation.map_sum_eq_of_lt ha hs
  change v (∑ i ∈ f.coeff.support, g i) = v (g a) at he
  change ∑ i ∈ f.coeff.support, g i = 0 at hy
  exact (v.ne_top_iff.mpr (mul_ne_zero (Finsupp.mem_support_iff.mp ha) (charVal y a).ne_zero))
    ((hy ▸ he).symm.trans v.map_zero)

-- A polynomial with no root of valuation zero has a unique least-valued coefficient.
private def Dominates (p : K[X]) (k : ℕ) (m : ℝ) : Prop :=
  v (p.coeff k) = m ∧ ∀ j, j ≠ k → (m : WithTop ℝ) < v (p.coeff j)

private lemma dominates_sub (p q : K[X]) {k : ℕ} {m : ℝ} (hp : Dominates v p k m)
    (hq : ∀ j, (m : WithTop ℝ) < v (q.coeff j)) : Dominates v (p - q) k m := by
  constructor
  · rw [coeff_sub, v.map_sub_eq_of_lt_left (hp.1.trans_lt (hq k)), hp.1]
  · intro j hj
    exact (lt_min (hp.2 j hj) (hq j)).trans_le (v.map_sub ..)

private lemma dominates_sub_right (p q : K[X]) {k : ℕ} {m : ℝ} (hq : Dominates v q k m)
    (hp : ∀ j, (m : WithTop ℝ) < v (p.coeff j)) : Dominates v (p - q) k m := by
  constructor
  · rw [coeff_sub, v.map_sub_eq_of_lt_right (hq.1.trans_lt (hp k)), hq.1]
  · intro j hj
    exact (lt_min (hp j) (hq.2 j hj)).trans_le (v.map_sub ..)

private lemma dominates_le {p : K[X]} {k : ℕ} {m : ℝ} (h : Dominates v p k m) (j : ℕ) :
    (m : WithTop ℝ) ≤ v (p.coeff j) := by
  rcases eq_or_ne j k with rfl | hne
  · exact h.1.ge
  · exact (h.2 _ hne).le

private lemma dominates_mul_linear {p : K[X]} {k : ℕ} {m : ℝ} (h : Dominates v p k m)
    {a : K} (ha : v a ≠ 0) : ∃ j r, Dominates v (p * (X - C a)) j r := by
  have hx : Dominates v (p * X) (k + 1) m := by
    refine ⟨by simpa only [coeff_mul_X] using h.1, ?_⟩
    rintro (_ | j) hj
    · simp
    · simpa only [coeff_mul_X] using h.2 j (by omega)
  rw [mul_sub]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
    have hbneg : b < 0 := by exact_mod_cast hb.trans_lt hneg
    have hlt : ((m + b : ℝ) : WithTop ℝ) < m := WithTop.coe_lt_coe.mpr (by linarith)
    refine ⟨k, m + b, dominates_sub_right v _ _ ⟨?_, ?_⟩
      (fun j ↦ hlt.trans_le (dominates_le v hx j))⟩
    · simp only [coeff_mul_C, v.map_mul, h.1, ← hb, WithTop.coe_add]
    · intro j hj
      simp only [coeff_mul_C, v.map_mul, ← hb, WithTop.coe_add]
      exact (add_lt_add_iff_left_of_ne_top (WithTop.coe_ne_top : (b : WithTop ℝ) ≠ ⊤)).mpr
        (h.2 j hj)
  · refine ⟨k + 1, m, dominates_sub v _ _ hx fun j ↦ ?_⟩
    rw [coeff_mul_C, v.map_mul]
    have hlt : (m : WithTop ℝ) + 0 < m + v a :=
      (add_lt_add_iff_right_of_ne_top WithTop.coe_ne_top).mpr hpos
    exact (by simpa using hlt : (m : WithTop ℝ) < m + v a).trans_le
      (add_le_add_left (dominates_le v h j) _)

private lemma dominates_of_no_root [IsAlgClosed K] (p : K[X]) (hp : p ≠ 0)
    (hroot : ∀ a, p.eval a = 0 → v a ≠ 0) : ∃ k m, Dominates v p k m := by
  classical
  have factors (s : Multiset K) (hs : ∀ a ∈ s, v a ≠ 0) :
      ∃ k m, Dominates v (C p.leadingCoeff * (s.map (X - C ·)).prod) k m := by
    induction s using Multiset.induction_on with
    | empty =>
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
        (v.ne_top_iff.mpr (leadingCoeff_ne_zero.mpr hp))
      refine ⟨0, r, ?_⟩
      simp only [Multiset.map_zero, Multiset.prod_zero, mul_one]
      exact ⟨by simpa using hr.symm, fun j hj ↦ by simp [coeff_C, hj]⟩
    | cons a s ih =>
      obtain ⟨k, m, h⟩ := ih (fun b hb ↦ hs b (Multiset.mem_cons_of_mem hb))
      simpa only [Multiset.map_cons, Multiset.prod_cons, mul_left_comm, mul_assoc, mul_comm]
        using dominates_mul_linear v h (hs a (Multiset.mem_cons_self ..))
  conv in Dominates v p _ _ => rw [(IsAlgClosed.splits p).eq_prod_roots]
  exact factors p.roots fun a ha ↦ hroot a ((mem_roots hp).mp ha)

-- Choose a monomial curve on which the finitely many exponent vectors stay distinct.
private lemma separating_direction (s : Finset (Fin n → ℤ)) :
    ∃ d : Fin n → ℤ, Set.InjOn (fun u : Fin n → ℤ ↦ ∑ i, d i * u i) s := by
  classical
  let P (u : Fin n → ℤ) : ℤ[X] := ∑ i : Fin n, monomial (i : ℕ) (u i)
  have coeffP (u : Fin n → ℤ) (i : Fin n) : (P u).coeff i = u i := by
    simp [P, coeff_monomial, Finsupp.single_apply, Fin.val_inj]
  have hev : ∀ᶠ t : ℤ in cofinite, ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (P a).eval t ≠ (P b).eval t := by
    apply (eventually_all_finset s).mpr
    intro a ha
    apply (eventually_all_finset s).mpr
    intro b hb
    by_cases h : a = b
    · simp [h]
    have hP : P a ≠ P b := fun he ↦ h (funext fun i ↦ by rw [← coeffP a i, he, coeffP])
    filter_upwards [eventually_eval_ne_zero_cofinite (sub_ne_zero.mpr hP)] with t ht
    simpa only [eval_sub, sub_ne_zero, ne_eq, h, not_false_eq_true, true_implies] using ht
  obtain ⟨t, ht⟩ := hev.exists
  refine ⟨fun i ↦ t ^ (i : ℕ), fun a ha b hb he ↦ by
    by_contra hn
    apply ht a ha b hb hn
    simpa [P, eval_finsetSum, mul_comm] using he⟩

private lemma monomial_curve [IsAlgClosed K] (f : LaurentPoly K n) (y : Fin n → Kˣ)
    (hw : (fun i ↦ (unitVal v (y i)).toAdd) ∈ tropicalHypersurface v f) :
    (fun i ↦ (unitVal v (y i)).toAdd) ∈ valuationsOfZeros v f := by
  classical
  obtain ⟨u, hu, u', hu', huu', he, hmin⟩ := hw
  let S := f.coeff.support
  obtain ⟨d, hd⟩ := separating_direction S
  let deg (a : Fin n → ℤ) := ∑ i, d i * a i
  obtain ⟨lo, hlo⟩ : BddBelow (deg '' (S : Set (Fin n → ℤ))) :=
    (S.finite_toSet.image deg).bddBelow
  -- Multiplying by a Laurent monomial shifts all curve exponents into ℕ.
  let e (a : Fin n → ℤ) := (deg a - lo).toNat
  have hedeg a (ha : a ∈ S) : (e a : ℤ) = deg a - lo :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hlo ⟨a, ha, rfl⟩))
  have hinj : Set.InjOn e S := by
    intro a ha b hb hab
    apply hd ha hb
    have h := congrArg Int.ofNat hab
    change (e a : ℤ) = (e b : ℤ) at h
    rw [hedeg a ha, hedeg b hb] at h
    change deg a = deg b
    omega
  let c (a : Fin n → ℤ) := f.coeff a * (charVal y a : K)
  let p : K[X] := ∑ a ∈ S, monomial (e a) (c a)
  -- Separation identifies each curve coefficient with a single original term.
  have hc a (ha : a ∈ S) : p.coeff (e a) = c a := by
    rw [show p.coeff (e a) = ∑ b ∈ S, (monomial (e b) (c b)).coeff (e a) by
      simp [p], Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      have hne : e b ≠ e a := fun h ↦ hba (hinj hb ha h)
      simp [coeff_monomial, hne]
    · simp [ha]
  have hvterm a : v (c a) = tropTerm v f (fun i ↦ (unitVal v (y i)).toAdd) a := by
    simp only [c, v.map_mul, ← coe_unitVal, charVal_val, tropTerm]
  have hp : p ≠ 0 := by
    intro h
    exact (mul_ne_zero (Finsupp.mem_support_iff.mp hu) (charVal y u).ne_zero)
      ((hc u hu).symm.trans (by simp [h]))
  have existsRoot : ∃ z, p.eval z = 0 ∧ v z = 0 := by
    by_contra! h
    obtain ⟨k, m, hdom⟩ := dominates_of_no_root v p hp h
    have hk : k ∈ S.image e := by
      by_contra hn
      have hk0 : p.coeff k = 0 := by
        simp only [p, finsetSum_coeff, coeff_monomial, Finsupp.single_apply]
        exact Finset.sum_eq_zero fun b hb ↦
          ite_eq_right (fun h ↦ hn (Finset.mem_image.mpr ⟨b, hb, h⟩))
      simpa [hk0] using hdom.1
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    have hleast : v (p.coeff (e u)) ≤ m := by
      rw [← hdom.1, hc u hu, hc b hb, hvterm, hvterm]
      exact hmin b hb
    have hleast' : v (p.coeff (e u')) ≤ m := by
      simpa only [hc u hu, hc u' hu', hvterm, ← he] using hleast
    have h₁ := hinj hu hb (show e u = e b from by_contra fun h ↦ (hdom.2 _ h).not_ge hleast)
    have h₂ := hinj hu' hb (show e u' = e b from by_contra fun h ↦ (hdom.2 _ h).not_ge hleast')
    exact huu' (h₁.trans h₂.symm)
  obtain ⟨z, hz, hzv⟩ := existsRoot
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hzv
  let t := Units.mk0 z hz0
  -- A root of valuation zero moves along the curve without changing coordinate valuations.
  let Y i := y i * t ^ d i
  have hchar (a : Fin n → ℤ) : charVal Y a = charVal y a * t ^ deg a := by
    simp only [Y, charVal, deg, mul_zpow, ← zpow_mul, Finset.prod_mul_distrib]
    congr 1
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => simp [hb, ih, zpow_add]
  refine ⟨Y, ?_, fun i ↦ ?_⟩
  · have heval : p.eval z = evalTorus f Y * ((t ^ (-lo) : Kˣ) : K) := by
      simp only [p, eval_finsetSum, eval_monomial, evalTorus, Finsupp.sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have heq : (t ^ e a : Kˣ) = t ^ deg a * t ^ (-lo) := by
        rw [← zpow_natCast, hedeg a ha, sub_eq_add_neg, zpow_add]
      have heq' := congrArg (fun x : Kˣ ↦ (x : K)) heq
      change c a * z ^ e a = f.coeff a * (charVal Y a : K) * _
      rw [hchar]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0, t] at heq'
      rw [heq']
      simp [c, mul_assoc, t]
    exact (mul_eq_zero.mp (heval.symm.trans hz)).resolve_right (Units.ne_zero _)
  · have ht : (unitVal v t).toAdd = 0 := WithTop.coe_injective ((coe_unitVal v t).trans hzv)
    rw [← coe_unitVal]
    congr 1
    simp [Y, map_zpow, ht]

-- The finite values form a rational vector space because every nonzero element has nth roots.
private def valueSpace [IsAlgClosed K] : Submodule ℚ ℝ where
  carrier := Set.range fun a : Kˣ ↦ (unitVal v a).toAdd
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  smul_mem' := by
    rintro q _ ⟨a, rfl⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) q.den_pos
    have hz0 : z ≠ 0 := fun he ↦ a.ne_zero (by simpa [he, q.den_nz] using hz.symm)
    let b := Units.mk0 z hz0
    have hp : b ^ q.den = a := Units.ext (by simpa [b] using hz)
    have h := congrArg (fun u ↦ (unitVal v u).toAdd) hp
    simp only [map_pow, toAdd_pow, nsmul_eq_mul] at h
    refine ⟨b ^ q.num, ?_⟩
    simp only [map_zpow, toAdd_zpow, zsmul_eq_mul, Rat.smul_def, Rat.cast_def, ← h]
    field_simp

private lemma valueSpace_dense [IsAlgClosed K] (hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) :
    Dense (valueSpace v : Set ℝ) := by
  obtain ⟨x, hx, hxv⟩ := hv
  let a := Units.mk0 x hx
  let r := (unitVal v a).toAdd
  have hr : r ≠ 0 := by
    intro h
    apply hxv
    rw [← show ((unitVal v a).toAdd : WithTop ℝ) = v x from coe_unitVal v a]
    exact_mod_cast h
  have hd : DenseRange (fun q : ℚ ↦ (q : ℝ) * r) :=
    (Homeomorph.mulRight₀ r hr).surjective.denseRange.comp Rat.denseRange_cast (by fun_prop)
  apply hd.mono
  rintro _ ⟨q, rfl⟩
  exact (valueSpace v).smul_mem q (show r ∈ valueSpace v from ⟨a, rfl⟩)

-- Approximate the identity pointwise by rational-linear maps into a dense subspace,
-- fixing that subspace. Consequently all equalities among finitely many weights persist.
private lemma linear_approx (V : Submodule ℚ ℝ) (hd : Dense (V : Set ℝ)) :
    ∃ A : ℕ → ℝ →ₗ[ℚ] ℝ, (∀ j x, A j x ∈ V) ∧ (∀ j, ∀ x ∈ V, A j x = x) ∧
      ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 x) := by
  classical
  obtain ⟨U, hU⟩ := V.exists_isCompl
  -- Approximate the basis vectors of the complement and extend linearly.
  let b := Module.Free.chooseBasis ℚ U
  have approx i := mem_closure_iff_seq_limit.mp (hd (b i : ℝ))
  choose z hmem hlim using approx
  let B (j : ℕ) := b.constr ℚ (fun i ↦ z i j)
  let A (j : ℕ) := V.projection U hU + (B j).comp (U.projectionOnto V hU.symm)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro j x
    apply V.add_mem (V.projection_apply_mem hU x)
    simp only [LinearMap.comp_apply, B, Module.Basis.constr_apply, Finsupp.sum]
    exact V.sum_mem fun i _ ↦ V.smul_mem _ (hmem i j)
  · intro j x hx
    simp [A, V.projection_apply_of_mem_left hU hx,
      (U.projectionOnto_apply_eq_zero_iff hU.symm).mpr hx]
  · intro x
    let u := U.projectionOnto V hU.symm x
    have hB : Tendsto (fun j ↦ B j u) atTop (𝓝 (u : ℝ)) := by
      conv in (u : ℝ) => rw [← U.subtype_apply u, ← b.constr_self ℚ U.subtype]
      simp only [B, Module.Basis.constr_apply, Finsupp.sum]
      exact tendsto_finsetSum _ fun i _ ↦ (hlim i).const_smul _
    have hsum := (tendsto_const_nhds (x := V.projection U hU x)).add hB
    simpa only [A, LinearMap.add_apply, LinearMap.comp_apply, u, Submodule.coe_projectionOnto_apply,
      Submodule.projection_add_projection_eq_self] using hsum

private lemma weight_map [IsAlgClosed K] (A : ℝ →ₗ[ℚ] ℝ)
    (hA : ∀ x ∈ valueSpace v, A x = x) (f : LaurentPoly K n)
    {a : Fin n → ℤ} (ha : a ∈ f.coeff.support) (w : Fin n → ℝ) :
    A (weight v f a w) = weight v f a (fun i ↦ A (w i)) := by
  let c := Units.mk0 (f.coeff a) (Finsupp.mem_support_iff.mp ha)
  have hc : (v (f.coeff a)).untopD 0 ∈ valueSpace v := by
    refine ⟨c, ?_⟩
    rw [← show ((unitVal v c).toAdd : WithTop ℝ) = v (f.coeff a) from coe_unitVal v c]
    simp
  simp only [weight, map_add, hA _ hc, map_sum, ← zsmul_eq_mul, map_zsmul]

private lemma approx_zero [IsAlgClosed K] (hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0)
    (f : LaurentPoly K n) : tropicalHypersurface v f ⊆ closure (valuationsOfZeros v f) := by
  classical
  rintro w ⟨a, ha, b, hb, hab, he, hm⟩
  obtain ⟨A, hmem, hfix, hlim⟩ := linear_approx (valueSpace v) (valueSpace_dense v hv)
  have hconv : Tendsto (fun j i ↦ A j (w i)) atTop (𝓝 w) :=
    tendsto_pi_nhds.mpr fun i ↦ hlim (w i)
  apply mem_closure_of_tendsto hconv
  have hmin : ∀ᶠ j in atTop, ∀ c ∈ f.coeff.support,
      A j (weight v f a w) ≤ A j (weight v f c w) := by
    apply (eventually_all_finset _).mpr
    intro c hc
    have h : weight v f a w ≤ weight v f c w := WithTop.coe_le_coe.mp (by
      simpa only [coe_weight v f ha, coe_weight v f hc] using hm c hc)
    rcases h.eq_or_lt with h | h
    · simp [h]
    · exact ((hlim _).eventually_lt (hlim _) h).mono fun _ h ↦ h.le
  filter_upwards [hmin] with j hj
  choose y hy using fun i ↦
    (show ∃ z : Kˣ, (unitVal v z).toAdd = A j (w i) from hmem j _)
  have he' : weight v f a w = weight v f b w := WithTop.coe_injective (by
    simpa only [coe_weight v f ha, coe_weight v f hb] using he)
  have hw : (fun i ↦ A j (w i)) ∈ tropicalHypersurface v f := by
    refine ⟨a, ha, b, hb, hab, ?_, ?_⟩
    · rw [← coe_weight v f ha, ← coe_weight v f hb, ← weight_map v _ (hfix j) f ha,
        ← weight_map v _ (hfix j) f hb, he']
    · intro c hc
      rw [← coe_weight v f ha, ← coe_weight v f hc, ← weight_map v _ (hfix j) f ha,
        ← weight_map v _ (hfix j) f hc]
      exact WithTop.coe_le_coe.mpr (hj c hc)
  rw [← funext hy] at hw ⊢
  exact monomial_curve v f y hw

/-- **Kapranov's theorem** (Maclagan–Sturmfels, *Introduction to Tropical Geometry*, draft of
4 November 2009, Theorem 3.1.3, equality of sets 1 and 3). Let `K` be an algebraically closed
field with a nontrivial valuation `val : K → ℝ ∪ {∞}` and `f` a nonzero Laurent polynomial in
`n` variables. Then the tropical hypersurface of `f` equals the closure in `ℝⁿ` of the set of
coordinatewise valuations of the zeros of `f` in the torus `(K^*)ⁿ`. (The hypothesis `f ≠ 0`
is implicit in the source: for `f = 0` the left side is empty and the right side is `ℝⁿ`.) -/
theorem tropicalHypersurface_eq_closure_valuationsOfZeros [IsAlgClosed K]
    (v : AddValuation K (WithTop ℝ)) (_hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0)
    (f : LaurentPoly K n) (_hf : f ≠ 0) :
    tropicalHypersurface v f = closure (valuationsOfZeros v f) :=
  Set.Subset.antisymm (approx_zero v _hv f)
    (closure_minimal (valuationsOfZeros_subset v f _hf) (hypersurface_closed v f))

end MathlibExt.AlgebraicGeometry.TropicalVarietyWanted
