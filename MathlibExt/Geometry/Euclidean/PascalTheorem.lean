/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

namespace MetaMathlibExt

@[expose] public section

/-- Explicit 2D determinant used to turn collinearity into polynomial equations. -/
private def D2 {k : Type*} [CommRing k] (x y : Fin 2 → k) : k := x 0 * y 1 - x 1 * y 0

private theorem D2_smul_right {k : Type*} [CommRing k] (x y : Fin 2 → k) (t : k) :
    D2 x (t • y) = t * D2 x y := by
  unfold D2
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem D2_self {k : Type*} [CommRing k] (x : Fin 2 → k) : D2 x x = 0 := by
  unfold D2
  ring

/-- Points collinear with `a, b` lie on the parametrized line through them. -/
private theorem line_param {k V P : Type*} [Field k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {a b q : P} (h : Collinear k ({a, b, q} : Set P)) (hne : b ≠ a) :
    ∃ t : k, q -ᵥ a = t • (b -ᵥ a) := by
  obtain ⟨p₀, vv, hrep⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp h
  obtain ⟨ra, rha⟩ := hrep a (by simp)
  obtain ⟨rb, rhb⟩ := hrep b (by simp)
  obtain ⟨rq, rhq⟩ := hrep q (by simp)
  have key : ∀ r s : k, (r • vv +ᵥ p₀) -ᵥ (s • vv +ᵥ p₀) = (r - s) • vv := by
    intro r s
    have h1 : ((r - s) • vv) +ᵥ (s • vv +ᵥ p₀) = r • vv +ᵥ p₀ := by
      rw [vadd_vadd, sub_smul, sub_add_cancel]
    conv_lhs => rw [← h1]
    exact vadd_vsub _ _
  have hba : b -ᵥ a = (rb - ra) • vv := by rw [rhb, rha]; exact key rb ra
  have hqa : q -ᵥ a = (rq - ra) • vv := by rw [rhq, rha]; exact key rq ra
  have hrbe : rb ≠ ra := by
    rintro rfl
    apply hne
    have hz : b -ᵥ a = (0 : V) := by rw [hba, sub_self, zero_smul]
    rwa [vsub_eq_zero_iff_eq] at hz
  refine ⟨(rq - ra) / (rb - ra), ?_⟩
  rw [hqa, hba, ← mul_smul, div_mul_cancel₀ (rq - ra) (sub_ne_zero.mpr hrbe)]

/-- **Pascal's theorem in an affine plane.** Let $k$ be a field of characteristic different from
$2$ and let $P$ be an affine plane over $k$, that is, an affine space whose space of translations
$V$ is a $k$-vector space of dimension $2$. Fix a point $O \in P$ and a nondegenerate symmetric
bilinear form $\beta$ on $V \times k$, and call the set of points $x \in P$ with
$\beta((x - O, 1), (x - O, 1)) = 0$ the conic. Let $v_0, v_1, \dots, v_5$ be six distinct points
of the conic such that, for each of the three pairs of opposite sides $(v_0 v_1, v_3 v_4)$,
$(v_1 v_2, v_4 v_5)$ and $(v_2 v_3, v_5 v_0)$ of the hexagon $v_0 v_1 v_2 v_3 v_4 v_5$, the four
endpoints are not collinear, so that the two lines are distinct. If $q_1$ lies on the lines
$v_0 v_1$ and $v_3 v_4$, $q_2$ lies on the lines $v_1 v_2$ and $v_4 v_5$, and $q_3$ lies on the
lines $v_2 v_3$ and $v_5 v_0$, then $q_1$, $q_2$, $q_3$ are collinear.

Source: https://en.wikipedia.org/wiki/Pascal%27s_theorem.
Proves `Wanted` entry `pascal_theorem`.
-/
theorem pascal_theorem {k V P : Type*} [Field k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    (hDim : Module.finrank k V = 2) (hChar : (2 : k) ≠ 0) (O : P) (v : Fin 6 → P)
    (B3 : LinearMap.BilinForm k (V × k))
    (hB3_symm : B3.IsSymm) (hB3_nondeg : B3.Nondegenerate)
    (q₁ q₂ q₃ : P)
    (hConic : ∀ i, B3 ((v i -ᵥ O), 1) ((v i -ᵥ O), 1) = 0)
    (hInj : Function.Injective v)
    (hLine₁ : ¬ Collinear k {v 0, v 1, v 3, v 4})
    (hLine₂ : ¬ Collinear k {v 1, v 2, v 4, v 5})
    (hLine₃ : ¬ Collinear k {v 2, v 3, v 5, v 0})
    (hMeet₁ : Collinear k {v 0, v 1, q₁} ∧ Collinear k {v 3, v 4, q₁})
    (hMeet₂ : Collinear k {v 1, v 2, q₂} ∧ Collinear k {v 4, v 5, q₂})
    (hMeet₃ : Collinear k {v 2, v 3, q₃} ∧ Collinear k {v 5, v 0, q₃}) :
    Collinear k {q₁, q₂, q₃} := by
  -- The two opposite-side directions through q₁.
  set u : V := v 1 -ᵥ v 0 with hu_def
  set w : V := v 4 -ᵥ v 3 with hw_def
  have hu0 : u ≠ 0 := vsub_ne_zero.mpr (hInj.ne (by decide : (1 : Fin 6) ≠ 0))
  have hw0 : w ≠ 0 := vsub_ne_zero.mpr (hInj.ne (by decide : (4 : Fin 6) ≠ 3))
  -- Parameters of q₁ on both lines through it.
  obtain ⟨t01, ht01⟩ := line_param hMeet₁.1 (hInj.ne (by decide : (1 : Fin 6) ≠ 0))
  obtain ⟨t34, ht34⟩ := line_param hMeet₁.2 (hInj.ne (by decide : (4 : Fin 6) ≠ 3))
  rw [← hu_def] at ht01
  rw [← hw_def] at ht34
  -- The directions are linearly independent (else all four points are collinear).
  have hLI : LinearIndependent k ![u, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      simp only [zero_smul, zero_add] at hst
      refine ⟨rfl, ?_⟩
      by_contra ht
      have htw : w = t⁻¹ • (t • w) := by rw [← mul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hst, smul_zero] at htw
      exact hw0 htw
    · exfalso
      have h1 : s • u = -(t • w) := eq_neg_of_add_eq_zero_left hst
      have h2 : u = s⁻¹ • (s • u) := by rw [← mul_smul, inv_mul_cancel₀ hs, one_smul]
      have hsc : u = (-t / s) • w := by
        have h3 : s⁻¹ • (-(t • w)) = (-t / s) • w := by
          have e : (-t / s) = -(s⁻¹ * t) := by rw [div_eq_mul_inv]; ring
          rw [e, smul_neg, ← mul_smul, ← neg_smul]
        rw [h2, h1]; exact h3
      have hneg : v 0 -ᵥ q₁ = (-t01) • u := by
        have h0 : v 0 -ᵥ q₁ + (q₁ -ᵥ v 0) = 0 := by
          rw [vsub_add_vsub_cancel, vsub_self]
        have h1' : v 0 -ᵥ q₁ = -(q₁ -ᵥ v 0) := eq_neg_of_add_eq_zero_left h0
        rw [h1', ht01, ← neg_smul]
      have hv03 : v 0 -ᵥ v 3 = ((-t01) * (-t / s) + t34) • w := by
        have h2' : v 0 -ᵥ v 3 = (v 0 -ᵥ q₁) + (q₁ -ᵥ v 3) :=
          (vsub_add_vsub_cancel _ _ _).symm
        rw [h2', hneg, ht34, hsc, ← mul_smul, ← add_smul]
      have hv13 : v 1 -ᵥ v 3 = ((-t / s) + ((-t01) * (-t / s) + t34)) • w := by
        have h2' : v 1 -ᵥ v 3 = (v 1 -ᵥ v 0) + (v 0 -ᵥ v 3) :=
          (vsub_add_vsub_cancel _ _ _).symm
        rw [h2', ← hu_def, hsc, hv03, ← add_smul]
      have hv43 : v 4 -ᵥ v 3 = (1 : k) • w := by rw [← hw_def, one_smul]
      have hcol : Collinear k ({v 0, v 1, v 3, v 4} : Set P) := by
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨v 3, w, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact ⟨((-t01) * (-t / s) + t34), by rw [← hv03, vsub_vadd]⟩
        · exact ⟨((-t / s) + ((-t01) * (-t / s) + t34)), by rw [← hv13, vsub_vadd]⟩
        · exact ⟨(0 : k), by rw [zero_smul, zero_vadd]⟩
        · exact ⟨(1 : k), by rw [← hv43, vsub_vadd]⟩
      exact absurd hcol hLine₁
  -- Basis adapted to the two directions; coordinates centered at q₁.
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by
    rw [Fintype.card_fin]; exact hDim.symm
  set b : Module.Basis (Fin 2) k V :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard with hb_def
  have hb0 : b 0 = u := by simp [hb_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = w := by simp [hb_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  set coord : P → Fin 2 → k := fun p => b.repr (p -ᵥ q₁) with hcoord_def
  have hrepr : ∀ (c : k) (i j : Fin 2), (b.repr (c • b i)) j = if i = j then c else 0 := by
    intro c i j
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs with h
    · exact mul_one _
    · exact mul_zero _
  -- Coordinate abbreviations (centered at q₁, axes along u, w).
  set s0 : k := coord (v 0) 0 with hs0_def
  set y0 : k := coord (v 0) 1 with hy0_def
  set s1 : k := coord (v 1) 0 with hs1_def
  set y1 : k := coord (v 1) 1 with hy1_def
  set x2 : k := coord (v 2) 0 with hx2_def
  set y2 : k := coord (v 2) 1 with hy2_def
  set x3 : k := coord (v 3) 0 with hx3_def
  set t3 : k := coord (v 3) 1 with ht3_def
  set x4 : k := coord (v 4) 0 with hx4_def
  set t4 : k := coord (v 4) 1 with ht4_def
  set x5 : k := coord (v 5) 0 with hx5_def
  set y5 : k := coord (v 5) 1 with hy5_def
  set X2 : k := coord q₂ 0 with hX2_def
  set Y2 : k := coord q₂ 1 with hY2_def
  set X3 : k := coord q₃ 0 with hX3_def
  set Y3 : k := coord q₃ 1 with hY3_def
  have hq1c : coord q₁ = 0 := by
    simp only [hcoord_def]
    simp [vsub_self]
  -- Vector differences in coordinates.
  have vsub_sub' : ∀ (a b q : P), a -ᵥ b = (a -ᵥ q) - (b -ᵥ q) := by
    intro a b q
    rw [eq_sub_iff_add_eq]
    exact vsub_add_vsub_cancel a b q
  have coord_smul : ∀ (a b q : P) (t : k), q -ᵥ a = t • (b -ᵥ a) →
      coord q - coord a = t • (coord b - coord a) := by
    intro p₁ p₂ q t ht
    have h : b.repr (q -ᵥ p₁) = t • b.repr (p₂ -ᵥ p₁) := by rw [ht, map_smul]
    rw [vsub_sub' q p₁ q₁, vsub_sub' p₂ p₁ q₁] at h
    funext i
    have hi := congrArg (· i) h
    simpa only [hcoord_def, Pi.sub_apply, Pi.smul_apply, map_sub, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul] using hi
  -- Axis vectors in coordinates.
  have hv0 : v 0 -ᵥ q₁ = (-t01) • b 0 := by
    have h0 : v 0 -ᵥ q₁ + (q₁ -ᵥ v 0) = 0 := by
      rw [vsub_add_vsub_cancel, vsub_self]
    have h1' : v 0 -ᵥ q₁ = -(q₁ -ᵥ v 0) := eq_neg_of_add_eq_zero_left h0
    rw [h1', ht01, ← neg_smul, hb0]
  have hv1 : v 1 -ᵥ q₁ = (1 - t01) • b 0 := by
    have h2 : v 1 -ᵥ q₁ = (v 1 -ᵥ v 0) + (v 0 -ᵥ q₁) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [h2, ← hu_def, hv0, hb0, sub_eq_add_neg, add_smul, one_smul]
  have hv3 : v 3 -ᵥ q₁ = (-t34) • b 1 := by
    have h0 : v 3 -ᵥ q₁ + (q₁ -ᵥ v 3) = 0 := by
      rw [vsub_add_vsub_cancel, vsub_self]
    have h1' : v 3 -ᵥ q₁ = -(q₁ -ᵥ v 3) := eq_neg_of_add_eq_zero_left h0
    rw [h1', ht34, ← neg_smul, hb1]
  have hv4 : v 4 -ᵥ q₁ = (1 - t34) • b 1 := by
    have h2 : v 4 -ᵥ q₁ = (v 4 -ᵥ v 3) + (v 3 -ᵥ q₁) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [h2, ← hw_def, hv3, hb1, sub_eq_add_neg, add_smul, one_smul]
  -- Axis facts: v₀, v₁ on the x-axis; v₃, v₄ on the y-axis.
  have hy0 : y0 = 0 := by
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have h : coord (v 0) 1 = 0 := by
      have h1 : coord (v 0) 1 = (b.repr ((-t01) • b 0)) 1 := by
        simpa only [hcoord_def] using congrArg (· 1) (congrArg b.repr hv0)
      rw [h1, hrepr]
      simp [h01]
    exact h
  have hy1 : y1 = 0 := by
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have h : coord (v 1) 1 = 0 := by
      have h1 : coord (v 1) 1 = (b.repr ((1 - t01) • b 0)) 1 := by
        simpa only [hcoord_def] using congrArg (· 1) (congrArg b.repr hv1)
      rw [h1, hrepr]
      simp [h01]
    exact h
  have hx3 : x3 = 0 := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h : coord (v 3) 0 = 0 := by
      have h1 : coord (v 3) 0 = (b.repr ((-t34) • b 1)) 0 := by
        simpa only [hcoord_def] using congrArg (· 0) (congrArg b.repr hv3)
      rw [h1, hrepr]
      simp [h10]
    exact h
  have hx4 : x4 = 0 := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h : coord (v 4) 0 = 0 := by
      have h1 : coord (v 4) 0 = (b.repr ((1 - t34) • b 1)) 0 := by
        simpa only [hcoord_def] using congrArg (· 0) (congrArg b.repr hv4)
      rw [h1, hrepr]
      simp [h10]
    exact h
  -- Distinctness along the axes.
  have he1 : s0 ≠ s1 := by
    intro hz
    apply hInj.ne (show (0 : Fin 6) ≠ 1 from by decide)
    have e0 : coord (v 0) 0 = coord (v 1) 0 := hz
    have e1' : coord (v 0) 1 = coord (v 1) 1 := by
      simp only [← hy0_def, ← hy1_def]
      rw [hy0, hy1]
    have hcc : coord (v 0) = coord (v 1) := by
      funext i
      fin_cases i
      · exact e0
      · exact e1'
    have hrr : b.repr (v 0 -ᵥ q₁) = b.repr (v 1 -ᵥ q₁) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact hz
      · exact hy0.trans hy1.symm
    have hvv : v 0 -ᵥ q₁ = v 1 -ᵥ q₁ := b.repr.injective hrr
    calc v 0 = (v 0 -ᵥ q₁) +ᵥ q₁ := (vsub_vadd _ _).symm
      _ = (v 1 -ᵥ q₁) +ᵥ q₁ := by rw [hvv]
      _ = v 1 := vsub_vadd _ _
  have he2 : t3 ≠ t4 := by
    intro hz
    apply hInj.ne (show (3 : Fin 6) ≠ 4 from by decide)
    have e0 : coord (v 3) 0 = coord (v 4) 0 := by
      simp only [← hx3_def, ← hx4_def]
      rw [hx3, hx4]
    have e1' : coord (v 3) 1 = coord (v 4) 1 := hz
    have hcc : coord (v 3) = coord (v 4) := by
      funext i
      fin_cases i
      · exact e0
      · exact e1'
    have hrr : b.repr (v 3 -ᵥ q₁) = b.repr (v 4 -ᵥ q₁) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact hx3.trans hx4.symm
      · exact hz
    have hvv : v 3 -ᵥ q₁ = v 4 -ᵥ q₁ := b.repr.injective hrr
    calc v 3 = (v 3 -ᵥ q₁) +ᵥ q₁ := (vsub_vadd _ _).symm
      _ = (v 4 -ᵥ q₁) +ᵥ q₁ := by rw [hvv]
      _ = v 4 := vsub_vadd _ _
  -- Conic coefficients in the q₁-centered frame.
  set e0 : V × k := (b 0, 0) with he0_def
  set e1 : V × k := (b 1, 0) with he1_def
  set eT : V × k := ((q₁ -ᵥ O), 1) with heT_def
  set A : k := B3 e0 e0 with hA_def
  set Bc : k := B3 e0 e1 + B3 e1 e0 with hBc_def
  set Cc : k := B3 e1 e1 with hCc_def
  set Dd : k := B3 e0 eT + B3 eT e0 with hDd_def
  set Ee : k := B3 e1 eT + B3 eT e1 with hEe_def
  set Ff : k := B3 eT eT with hFf_def
  have hexpand : ∀ x0 x1 : k, B3 ((x0 • b 0 + x1 • b 1 + (q₁ -ᵥ O)), 1)
      ((x0 • b 0 + x1 • b 1 + (q₁ -ᵥ O)), 1)
      = A * x0 ^ 2 + Bc * x0 * x1 + Cc * x1 ^ 2 + Dd * x0 + Ee * x1 + Ff := by
    intro x0 x1
    have hz : ((x0 • b 0 + x1 • b 1 + (q₁ -ᵥ O)), (1 : k))
        = x0 • e0 + x1 • e1 + eT := by
      ext <;> simp [he0_def, he1_def, heT_def, Prod.mk_add_mk, Prod.smul_mk]
    rw [hz]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hA_def, hBc_def, hCc_def, hDd_def, hEe_def, hFf_def]
    rw [hB3_symm.eq e1 e0, hB3_symm.eq eT e0, hB3_symm.eq eT e1]
    ring
  -- Coordinate decompositions of the six points.
  have hrepr2 : ∀ (x : V), x = (b.repr x) 0 • b 0 + (b.repr x) 1 • b 1 := by
    intro x
    have h := (b.sum_repr x).symm
    rwa [Fin.sum_univ_two] at h
  have hvr0 : v 0 -ᵥ q₁ = s0 • b 0 + y0 • b 1 := hrepr2 _
  have hvr1 : v 1 -ᵥ q₁ = s1 • b 0 + y1 • b 1 := hrepr2 _
  have hvr2 : v 2 -ᵥ q₁ = x2 • b 0 + y2 • b 1 := hrepr2 _
  have hvr3 : v 3 -ᵥ q₁ = x3 • b 0 + t3 • b 1 := hrepr2 _
  have hvr4 : v 4 -ᵥ q₁ = x4 • b 0 + t4 • b 1 := hrepr2 _
  have hvr5 : v 5 -ᵥ q₁ = x5 • b 0 + y5 • b 1 := hrepr2 _
  -- The six conic equations.
  have hC0 : A * s0 ^ 2 + Dd * s0 + Ff = 0 := by
    have h := hConic 0
    have hvo : v 0 -ᵥ O = s0 • b 0 + y0 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 0 -ᵥ O = (v 0 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr0]
    rw [hvo, hexpand, hy0] at h
    linear_combination h
  have hC1 : A * s1 ^ 2 + Dd * s1 + Ff = 0 := by
    have h := hConic 1
    have hvo : v 1 -ᵥ O = s1 • b 0 + y1 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 1 -ᵥ O = (v 1 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr1]
    rw [hvo, hexpand, hy1] at h
    linear_combination h
  have hC3 : Cc * t3 ^ 2 + Ee * t3 + Ff = 0 := by
    have h := hConic 3
    have hvo : v 3 -ᵥ O = x3 • b 0 + t3 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 3 -ᵥ O = (v 3 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr3]
    rw [hvo, hexpand, hx3] at h
    linear_combination h
  have hC4 : Cc * t4 ^ 2 + Ee * t4 + Ff = 0 := by
    have h := hConic 4
    have hvo : v 4 -ᵥ O = x4 • b 0 + t4 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 4 -ᵥ O = (v 4 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr4]
    rw [hvo, hexpand, hx4] at h
    linear_combination h
  have hC2 : A * x2 ^ 2 + Bc * x2 * y2 + Cc * y2 ^ 2 + Dd * x2 + Ee * y2 + Ff = 0 := by
    have h := hConic 2
    have hvo : v 2 -ᵥ O = x2 • b 0 + y2 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 2 -ᵥ O = (v 2 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr2]
    rw [hvo, hexpand] at h
    exact h
  have hC5 : A * x5 ^ 2 + Bc * x5 * y5 + Cc * y5 ^ 2 + Dd * x5 + Ee * y5 + Ff = 0 := by
    have h := hConic 5
    have hvo : v 5 -ᵥ O = x5 • b 0 + y5 • b 1 + (q₁ -ᵥ O) := by
      have h2 : v 5 -ᵥ O = (v 5 -ᵥ q₁) + (q₁ -ᵥ O) :=
        (vsub_add_vsub_cancel _ _ _).symm
      rw [h2, hvr5]
    rw [hvo, hexpand] at h
    exact h
  -- Incidence equations for q₂, q₃.
  obtain ⟨t12, ht12⟩ := line_param hMeet₂.1 (hInj.ne (by decide : (2 : Fin 6) ≠ 1))
  obtain ⟨t45, ht45⟩ := line_param hMeet₂.2 (hInj.ne (by decide : (5 : Fin 6) ≠ 4))
  obtain ⟨t23, ht23⟩ := line_param hMeet₃.1 (hInj.ne (by decide : (3 : Fin 6) ≠ 2))
  obtain ⟨t50, ht50⟩ := line_param hMeet₃.2 (hInj.ne (by decide : (0 : Fin 6) ≠ 5))
  have e12 := coord_smul _ _ _ _ ht12
  have e45 := coord_smul _ _ _ _ ht45
  have e23 := coord_smul _ _ _ _ ht23
  have e50 := coord_smul _ _ _ _ ht50
  have hX12 : X2 - s1 = t12 * (x2 - s1) := by
    have h := congrArg (· 0) e12
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hY12 : Y2 - y1 = t12 * (y2 - y1) := by
    have h := congrArg (· 1) e12
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hX45 : X2 - x4 = t45 * (x5 - x4) := by
    have h := congrArg (· 0) e45
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hY45 : Y2 - t4 = t45 * (y5 - t4) := by
    have h := congrArg (· 1) e45
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hX23 : X3 - x2 = t23 * (x3 - x2) := by
    have h := congrArg (· 0) e23
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hY23 : Y3 - y2 = t23 * (t3 - y2) := by
    have h := congrArg (· 1) e23
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hX50 : X3 - x5 = t50 * (s0 - x5) := by
    have h := congrArg (· 0) e50
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hY50 : Y3 - y5 = t50 * (y0 - y5) := by
    have h := congrArg (· 1) e50
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  rw [hy1] at hY12
  rw [hx4] at hX45
  rw [hx3] at hX23
  rw [hy0] at hY50
  have hL2a : (x2 - s1) * Y2 - y2 * (X2 - s1) = 0 := by
    linear_combination (x2 - s1) * hY12 - y2 * hX12
  have hL2b : x5 * (Y2 - t4) - (y5 - t4) * X2 = 0 := by
    linear_combination x5 * hY45 - (y5 - t4) * hX45
  have hL3a : x2 * (Y3 - t3) - (y2 - t3) * X3 = 0 := by
    linear_combination x2 * hY23 - (y2 - t3) * hX23
  have hL3b : (x5 - s0) * Y3 - y5 * (X3 - s0) = 0 := by
    linear_combination (x5 - s0) * hY50 - y5 * hX50
  -- Coordinate differences detect distinct points.
  have coord_ne : ∀ (a b : P), b ≠ a → coord b - coord a ≠ 0 := by
    intro p₁ p₂ hne hz
    apply hne
    have hcb : coord p₂ = coord p₁ := sub_eq_zero.mp hz
    have hrr : b.repr (p₂ -ᵥ q₁) = b.repr (p₁ -ᵥ q₁) := by
      apply Finsupp.ext
      intro i
      have hi := congrFun hcb i
      simpa only [hcoord_def] using hi
    have hvv : p₂ -ᵥ q₁ = p₁ -ᵥ q₁ := b.repr.injective hrr
    calc p₂ = (p₂ -ᵥ q₁) +ᵥ q₁ := (vsub_vadd _ _).symm
      _ = (p₁ -ᵥ q₁) +ᵥ q₁ := by rw [hvv]
      _ = p₁ := vsub_vadd _ _
  -- Transversality: distinct intersecting lines have non-parallel directions.
  have transv : ∀ (p₁ p₂ p₃ p₄ q : P), p₂ ≠ p₁ → p₄ ≠ p₃ →
      Collinear k ({p₁, p₂, q} : Set P) → Collinear k ({p₃, p₄, q} : Set P) →
      ¬ Collinear k ({p₁, p₂, p₃, p₄} : Set P) →
      D2 (coord p₂ - coord p₁) (coord p₄ - coord p₃) ≠ 0 := by
    intro p₁ p₂ p₃ p₄ q hne1 hne2 h1 h2 hnc hD
    obtain ⟨t, ht⟩ := line_param h1 hne1
    obtain ⟨s, hs⟩ := line_param h2 hne2
    have e1 : coord q - coord p₁ = t • (coord p₂ - coord p₁) := coord_smul _ _ _ _ ht
    have e2 : coord q - coord p₃ = s • (coord p₄ - coord p₃) := coord_smul _ _ _ _ hs
    have hw1 : coord p₂ - coord p₁ ≠ 0 := coord_ne _ _ hne1
    have hw2 : coord p₄ - coord p₃ ≠ 0 := coord_ne _ _ hne2
    set w1 : Fin 2 → k := coord p₂ - coord p₁ with hw1d
    set w2 : Fin 2 → k := coord p₄ - coord p₃ with hw2d
    have hD' : w1 0 * w2 1 - w1 1 * w2 0 = 0 := hD
    have hdep : ∃ cc : k, w1 = cc • w2 := by
      by_cases hX : w2 0 = 0
      · have hY : w2 1 ≠ 0 := by
          intro hz
          apply hw2
          funext i
          fin_cases i
          · exact hX
          · exact hz
        refine ⟨w1 1 / w2 1, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · have hw10 : w1 0 = 0 := by
            have hww : w1 0 * w2 1 = w1 1 * w2 0 := by linear_combination hD'
            rw [hX, mul_zero] at hww
            exact (mul_eq_zero.mp hww).resolve_right hY
          rw [Pi.smul_apply, smul_eq_mul, hX, mul_zero]
          exact hw10
        · rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hY]
      · refine ⟨w1 0 / w2 0, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
        · rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hX]
        · have hww : w1 0 * w2 1 = w1 1 * w2 0 := by linear_combination hD'
          rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hX]
          exact hww.symm
    obtain ⟨cc, hcc⟩ := hdep
    have hvec : p₂ -ᵥ p₁ = cc • (p₄ -ᵥ p₃) := by
      apply b.repr.injective
      rw [map_smul, vsub_sub' p₂ p₁ q₁, vsub_sub' p₄ p₃ q₁, map_sub, map_sub]
      apply Finsupp.ext
      intro i
      have hi := congrFun hcc i
      simpa only [hw1d, hw2d, hcoord_def, Pi.sub_apply, Pi.smul_apply,
        Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] using hi
    have ha : p₁ -ᵥ q = ((-t) * cc) • (p₄ -ᵥ p₃) := by
      have h1 : p₁ -ᵥ q = -(q -ᵥ p₁) := by
        have h0 : p₁ -ᵥ q + (q -ᵥ p₁) = 0 := by rw [vsub_add_vsub_cancel, vsub_self]
        exact eq_neg_of_add_eq_zero_left h0
      rw [h1, ht, hvec, ← neg_smul, ← mul_smul]
    have hb : p₂ -ᵥ q = ((1 - t) * cc) • (p₄ -ᵥ p₃) := by
      have h2 : p₂ -ᵥ q = (p₂ -ᵥ p₁) + (p₁ -ᵥ q) := (vsub_add_vsub_cancel _ _ _).symm
      have e : cc + (-t) * cc = (1 - t) * cc := by ring
      rw [h2, hvec, ha, ← add_smul, e]
    have hc : p₃ -ᵥ q = (-s) • (p₄ -ᵥ p₃) := by
      have h1 : p₃ -ᵥ q = -(q -ᵥ p₃) := by
        have h0 : p₃ -ᵥ q + (q -ᵥ p₃) = 0 := by rw [vsub_add_vsub_cancel, vsub_self]
        exact eq_neg_of_add_eq_zero_left h0
      rw [h1, hs, ← neg_smul]
    have hd : p₄ -ᵥ q = (1 - s) • (p₄ -ᵥ p₃) := by
      have h2 : p₄ -ᵥ q = (p₄ -ᵥ p₃) + (p₃ -ᵥ q) := (vsub_add_vsub_cancel _ _ _).symm
      have e : (1 : k) + (-s) = 1 - s := by ring
      rw [h2, hc, ← e, add_smul, one_smul]
    have hcol : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨q, (p₄ -ᵥ p₃), ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨((-t) * cc), by rw [← ha, vsub_vadd]⟩
      · exact ⟨((1 - t) * cc), by rw [← hb, vsub_vadd]⟩
      · exact ⟨(-s), by rw [← hc, vsub_vadd]⟩
      · exact ⟨(1 - s), by rw [← hd, vsub_vadd]⟩
    exact absurd hcol hnc
  have D2coords : ∀ (p q r s : P), D2 (coord q - coord p) (coord s - coord r)
      = ((coord q 0 - coord p 0) * (coord s 1 - coord r 1)
        - (coord q 1 - coord p 1) * (coord s 0 - coord r 0)) := by
    intro p q r s
    unfold D2
    simp only [Pi.sub_apply]
  have hd2 : (x2 - s1) * (y5 - t4) - y2 * x5 ≠ 0 := by
    have h := transv (v 1) (v 2) (v 4) (v 5) q₂
      (hInj.ne (by decide : (2 : Fin 6) ≠ 1)) (hInj.ne (by decide : (5 : Fin 6) ≠ 4))
      hMeet₂.1 hMeet₂.2 hLine₂
    have e : D2 (coord (v 2) - coord (v 1)) (coord (v 5) - coord (v 4))
        = (x2 - s1) * (y5 - t4) - y2 * x5 := by
      rw [D2coords]
      simp only [← hs1_def, ← hx2_def, ← hy2_def, ← hy1_def, ← hx4_def, ← ht4_def,
        ← hx5_def, ← hy5_def]
      rw [hy1, hx4]
      ring
    rwa [e] at h
  have hd3 : x2 * y5 - (t3 - y2) * (s0 - x5) ≠ 0 := by
    have h := transv (v 2) (v 3) (v 5) (v 0) q₃
      (hInj.ne (by decide : (3 : Fin 6) ≠ 2)) (hInj.ne (by decide : (0 : Fin 6) ≠ 5))
      hMeet₃.1 hMeet₃.2 hLine₃
    have e : D2 (coord (v 3) - coord (v 2)) (coord (v 0) - coord (v 5))
        = x2 * y5 - (t3 - y2) * (s0 - x5) := by
      rw [D2coords]
      simp only [← hx2_def, ← hy2_def, ← hx3_def, ← ht3_def, ← hs0_def, ← hy0_def,
        ← hx5_def, ← hy5_def]
      rw [hx3, hy0]
      ring
    rwa [e] at h
  -- Conic coefficient relations.
  set f1 : k := s0 - s1 with hf1_def
  set f2 : k := t3 - t4 with hf2_def
  have hf1' : f1 ≠ 0 := sub_ne_zero.mpr he1
  have hf2' : f2 ≠ 0 := sub_ne_zero.mpr he2
  have hDd : f1 * (A * (s0 + s1) + Dd) = 0 := by linear_combination hC0 - hC1
  have hE : f2 * (Cc * (t3 + t4) + Ee) = 0 := by linear_combination hC3 - hC4
  have hF : f1 * Ff = f1 * A * s0 * s1 := by
    linear_combination (f1 - s0) * hC0 + s0 * hC1
  have hF2 : f2 * Ff = f2 * Cc * t3 * t4 := by
    linear_combination (f2 - t3) * hC3 + t3 * hC4
  -- Reduced conic equations.
  set U2 : k := (x2 - s0) * (x2 - s1) with hU2_def
  set V2 : k := x2 * y2 with hV2_def
  set W2s : k := (y2 - t3) * (y2 - t4) - t3 * t4 with hW2s_def
  set U5 : k := (x5 - s0) * (x5 - s1) with hU5_def
  set V5 : k := x5 * y5 with hV5_def
  set W5s : k := (y5 - t3) * (y5 - t4) - t3 * t4 with hW5s_def
  have hE2 : A * U2 + Bc * V2 + Cc * W2s = 0 := by
    have hE2' : f1 * f2 * (A * U2 + Bc * V2 + Cc * W2s) = 0 := by
      linear_combination f1 * f2 * hC2 - x2 * f2 * hC0 + x2 * f2 * hC1
        - y2 * f1 * hC3 + y2 * f1 * hC4 - f2 * hF
    exact (mul_eq_zero.mp hE2').resolve_left (mul_ne_zero hf1' hf2')
  have hE5 : A * U5 + Bc * V5 + Cc * W5s = 0 := by
    have hE5' : f1 * f2 * (A * U5 + Bc * V5 + Cc * W5s) = 0 := by
      linear_combination f1 * f2 * hC5 - x5 * f2 * hC0 + x5 * f2 * hC1
        - y5 * f1 * hC3 + y5 * f1 * hC4 - f2 * hF
    exact (mul_eq_zero.mp hE5').resolve_left (mul_ne_zero hf1' hf2')
  have hK : A * s0 * s1 - Cc * t3 * t4 = 0 := by
    have hK' : f1 * f2 * (A * s0 * s1 - Cc * t3 * t4) = 0 := by
      linear_combination -f2 * hF + f1 * hF2
    exact (mul_eq_zero.mp hK').resolve_left (mul_ne_zero hf1' hf2')
  -- The 3×3 determinant vanishes by nondegeneracy.
  set M3 : Matrix (Fin 3) (Fin 3) k :=
    ![![U2, V2, W2s], ![U5, V5, W5s], ![s0 * s1, 0, -(t3 * t4)]] with hM3_def
  set D3c : k := U2 * V5 * (-(t3 * t4)) - V2 * U5 * (-(t3 * t4))
    + V2 * W5s * (s0 * s1) - W2s * V5 * (s0 * s1) with hD3c_def
  have hM3 : M3.mulVec ![A, Bc, Cc] = 0 := by
    have e : M3.mulVec ![A, Bc, Cc]
        = ![A * U2 + Bc * V2 + Cc * W2s, A * U5 + Bc * V5 + Cc * W5s,
            A * (s0 * s1) + Cc * (-(t3 * t4))] := by
      funext i
      fin_cases i
      · simp [Matrix.mulVec, hM3_def]
        ring
      · simp [Matrix.mulVec, hM3_def]
        ring
      · simp [Matrix.mulVec, hM3_def]
        ring
    have hK0 : A * (s0 * s1) + Cc * (-(t3 * t4)) = 0 := by linear_combination hK
    rw [e, hE2, hE5, hK0]
    ext i
    fin_cases i <;> rfl
  have hdet : M3.det = D3c := by
    rw [Matrix.det_fin_three]
    simp [hM3_def]
    ring
  have hD3 : D3c = 0 := by
    by_contra hne
    have hdetne : M3.det ≠ 0 := by rwa [hdet]
    have hv0 : ![A, Bc, Cc] = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetne hM3
    have hA0 : A = 0 := by have h := congrArg (· 0) hv0; simpa using h
    have hBc0 : Bc = 0 := by have h := congrArg (· 1) hv0; simpa using h
    have hCc0 : Cc = 0 := by have h := congrArg (· 2) hv0; simpa using h
    have hDd0 : Dd = 0 := by
      have h := hDd
      simp [hA0] at h
      exact h.resolve_left hf1'
    have hEe0 : Ee = 0 := by
      have h := hE
      simp [hCc0] at h
      exact h.resolve_left hf2'
    have hFf0 : Ff = 0 := by
      have h := hF
      simp [hA0] at h
      exact h.resolve_left hf1'
    set x : V × k := ((q₁ -ᵥ O), 1) with hx_def
    have hx0 : x ≠ 0 := by
      intro hz
      have h1 : (1 : k) = 0 := by
        have h2 := congrArg Prod.snd hz
        simpa [hx_def] using h2
      exact one_ne_zero h1
    have hxe0 : B3 x e0 = 0 := by
      have hde : B3 e0 eT + B3 eT e0 = 0 := hDd0
      have hsym : B3 e0 eT = B3 x e0 := hB3_symm.eq e0 eT
      have hxx : B3 eT e0 = B3 x e0 := rfl
      rw [hsym, hxx] at hde
      have h2 : (2 : k) * (B3 x e0) = 0 := by linear_combination hde
      exact (mul_eq_zero.mp h2).resolve_left hChar
    have hxe1 : B3 x e1 = 0 := by
      have hde : B3 e1 eT + B3 eT e1 = 0 := hEe0
      have hsym : B3 e1 eT = B3 x e1 := hB3_symm.eq e1 eT
      have hxx : B3 eT e1 = B3 x e1 := rfl
      rw [hsym, hxx] at hde
      have h2 : (2 : k) * (B3 x e1) = 0 := by linear_combination hde
      exact (mul_eq_zero.mp h2).resolve_left hChar
    have hxx : B3 x x = 0 := hFf0
    have hxB : ∀ y : V × k, B3 x y = 0 := by
      intro y
      obtain ⟨w, c⟩ := y
      have hyc : (w, c) = ((w - c • (q₁ -ᵥ O)), 0) + c • x := by
        rw [hx_def, Prod.smul_mk, Prod.mk_add_mk]
        ext <;> simp [sub_add_cancel, smul_eq_mul]
      have hwc : ((w - c • (q₁ -ᵥ O)), (0 : k))
          = (b.repr (w - c • (q₁ -ᵥ O))) 0 • e0
            + (b.repr (w - c • (q₁ -ᵥ O))) 1 • e1 := by
        have hfst := hrepr2 (w - c • (q₁ -ᵥ O))
        rw [he0_def, he1_def, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk]
        exact Prod.ext hfst (by simp)
      rw [hyc, map_add, hwc, map_add, map_smul, map_smul, map_smul, hxe0, hxe1, hxx]
      simp
    have hcontra : x = 0 := hB3_nondeg.1 x hxB
    exact hx0 hcontra
  -- Cramer numerators for q₂, q₃.
  set d2 : k := (-y2) * x5 - (x2 - s1) * (-(y5 - t4)) with hd2_def
  set d3 : k := (-(y2 - t3)) * (x5 - s0) - (x2) * (-y5) with hd3_def
  set X2n : k := (-y2 * s1) * x5 - (x2 - s1) * (x5 * t4) with hX2n_def
  set Y2n : k := (-y2) * (x5 * t4) - (-y2 * s1) * (-(y5 - t4)) with hY2n_def
  set X3n : k := (x2 * t3) * (x5 - s0) - (x2) * (-y5 * s0) with hX3n_def
  set Y3n : k := (-(y2 - t3)) * (-y5 * s0) - (x2 * t3) * (-y5) with hY3n_def
  have hd2' : d2 ≠ 0 := by
    have e : d2 = (x2 - s1) * (y5 - t4) - y2 * x5 := by ring
    rw [e]; exact hd2
  have hd3' : d3 ≠ 0 := by
    have e : d3 = x2 * y5 - (t3 - y2) * (s0 - x5) := by ring
    rw [e]; exact hd3
  have hCr1 : d2 * X2 = X2n := by
    linear_combination x5 * hL2a - (x2 - s1) * hL2b
  have hCr2 : d2 * Y2 = Y2n := by
    linear_combination (y5 - t4) * hL2a - y2 * hL2b
  have hCr3 : d3 * X3 = X3n := by
    linear_combination (x5 - s0) * hL3a - x2 * hL3b
  have hCr4 : d3 * Y3 = Y3n := by
    linear_combination y5 * hL3a - (y2 - t3) * hL3b
  have hDD : d2 * d3 * (X2 * Y3 - X3 * Y2) = X2n * Y3n - X3n * Y2n := by
    linear_combination (d3 * Y3) * hCr1 - (d3 * X3) * hCr2
      - Y2n * hCr3 + X2n * hCr4
  have hN : X2n * Y3n - X3n * Y2n = D3c := by ring
  have hDgoal : X2 * Y3 - X3 * Y2 = 0 := by
    have h0 : d2 * d3 * (X2 * Y3 - X3 * Y2) = 0 := by rw [hDD, hN, hD3]
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hd2' hd3')
  -- Assemble collinearity of q₁, q₂, q₃.
  by_cases hq : q₂ = q₁
  · rw [hq]
    have hset : ({q₁, q₁, q₃} : Set P) = {q₁, q₃} := Set.insert_idem _ _
    rw [hset]
    exact collinear_pair k q₁ q₃
  · have hD2 : X2 * Y3 - X3 * Y2 = 0 := hDgoal
    obtain ⟨r, hrX, hrY⟩ : ∃ r : k, X3 = r * X2 ∧ Y3 = r * Y2 := by
      by_cases hX : X2 = 0
      · rw [hX, zero_mul, zero_sub, neg_eq_zero] at hD2
        by_cases hY : Y2 = 0
        · exfalso
          apply hq
          have e0 : coord q₂ 0 = coord q₁ 0 := by
            have h1 : coord q₂ 0 = 0 := hX
            have h2 : coord q₁ 0 = 0 := by rw [hq1c]; rfl
            rw [h1, h2]
          have e1' : coord q₂ 1 = coord q₁ 1 := by
            have h1 : coord q₂ 1 = 0 := hY
            have h2 : coord q₁ 1 = 0 := by rw [hq1c]; rfl
            rw [h1, h2]
          have hcc : coord q₂ = coord q₁ :=
            funext (Fin.forall_fin_two.mpr ⟨e0, e1'⟩)
          have hrr : b.repr (q₂ -ᵥ q₁) = b.repr (q₁ -ᵥ q₁) := by
            apply Finsupp.ext
            intro i
            have hi := congrFun hcc i
            simpa only [hcoord_def] using hi
          have hvv : q₂ -ᵥ q₁ = q₁ -ᵥ q₁ := b.repr.injective hrr
          have hqq : q₂ = q₁ := by
            calc q₂ = (q₂ -ᵥ q₁) +ᵥ q₁ := (vsub_vadd _ _).symm
              _ = (q₁ -ᵥ q₁) +ᵥ q₁ := by rw [hvv]
              _ = q₁ := by rw [vsub_self, zero_vadd]
          exact hqq
        · have hX3 : X3 = 0 := (mul_eq_zero.mp hD2).resolve_right hY
          refine ⟨Y3 / Y2, ?_, ?_⟩
          · rw [hX3, hX, mul_zero]
          · rw [div_mul_cancel₀ _ hY]
      · refine ⟨X3 / X2, ?_, ?_⟩
        · rw [div_mul_cancel₀ _ hX]
        · have hmul : Y3 * X2 = (X3 / X2) * Y2 * X2 := by
            have h1 : (X3 / X2) * Y2 * X2 = ((X3 / X2) * X2) * Y2 := by ring
            rw [h1, div_mul_cancel₀ _ hX]
            linear_combination hDgoal
          exact mul_right_cancel₀ hX hmul
    have hcc3 : coord q₃ = r • coord q₂ := by
      funext i
      fin_cases i
      · show coord q₃ 0 = (r • coord q₂) 0
        rw [Pi.smul_apply, smul_eq_mul]
        exact hrX
      · show coord q₃ 1 = (r • coord q₂) 1
        rw [Pi.smul_apply, smul_eq_mul]
        exact hrY
    have hrr3 : b.repr (q₃ -ᵥ q₁) = b.repr (r • (q₂ -ᵥ q₁)) := by
      rw [map_smul]
      apply Finsupp.ext
      intro i
      have hi := congrFun hcc3 i
      simpa only [hcoord_def, Pi.smul_apply, Finsupp.smul_apply, smul_eq_mul] using hi
    have hvv3 : q₃ -ᵥ q₁ = r • (q₂ -ᵥ q₁) := b.repr.injective hrr3
    have hq3 : q₃ = r • (q₂ -ᵥ q₁) +ᵥ q₁ := by rw [← hvv3, vsub_vadd]
    have hfin : Collinear k ({q₁, q₂, q₃} : Set P) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨q₁, (q₂ -ᵥ q₁), ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨(0 : k), by rw [zero_smul, zero_vadd]⟩
      · exact ⟨(1 : k), by rw [one_smul, vsub_vadd]⟩
      · exact ⟨r, hq3⟩
    exact hfin

end

end MetaMathlibExt
