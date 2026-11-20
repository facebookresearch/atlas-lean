/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Perfect-complements (Leontief) demand

For the utility `u(x) = min (a x₀) (b x₁)` with `a, b > 0`, positive prices and nonnegative
wealth, the demanded bundle is the kink `(t / a, t / b)` with `t = w / (p₀ / a + p₁ / b)`: the
cheapest bundle on the ray `a x₀ = b x₁` that exhausts wealth. The optimality proof is order and
linear arithmetic; at the kink the utility is not differentiable, so first-order conditions are
not available there.

## Main definitions

* `leontief a b`: the utility `min (a x₀) (b x₁)`.
* `leontiefDemand a b p w`: the kink bundle.

## Main results

* `isMarshallianDemand_leontief`: the kink bundle is a Marshallian demand on the nonnegative
  orthant.
* `not_differentiableAt_leontief_leontiefDemand`: for `w > 0`, `leontief a b` is not
  differentiable at the demanded bundle.

Atlas roadmap target EC03.T04.

## References

* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 5.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), ch. 3.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The perfect-complements (Leontief) utility `u(x) = min (a x₀) (b x₁)`. -/
noncomputable def leontief (a b : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  min (a * x 0) (b * x 1)

/-- The kink bundle `(t / a, t / b)` with `t = w / (p₀ / a + p₁ / b)`: the cheapest bundle
on the ray `a x₀ = b x₁` that exhausts wealth. -/
noncomputable def leontiefDemand (a b : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![w / (p 0 / a + p 1 / b) / a, w / (p 0 / a + p 1 / b) / b]

/-- **Perfect-complements demand.** With positive coefficients, positive prices and
nonnegative wealth, the kink bundle maximizes `leontief a b` over the budget set in the
nonnegative orthant. -/
theorem isMarshallianDemand_leontief {a b w : ℝ} {p : Fin 2 → ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : ∀ i, 0 < p i) (hw : 0 ≤ w) :
    IsMarshallianDemand (leontief a b) twoGoodSet p w (leontiefDemand a b p w) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hp0 : 0 < p 0 := hp 0
  have hp1 : 0 < p 1 := hp 1
  have hS0 : 0 < p 0 / a + p 1 / b := add_pos (div_pos hp0 ha) (div_pos hp1 hb)
  have hS' : p 0 / a + p 1 / b ≠ 0 := ne_of_gt hS0
  have ht0 : 0 ≤ w / (p 0 / a + p 1 / b) := div_nonneg hw (le_of_lt hS0)
  have hx0 : leontiefDemand a b p w 0 = w / (p 0 / a + p 1 / b) / a := by
    simp [leontiefDemand]
  have hx1 : leontiefDemand a b p w 1 = w / (p 0 / a + p 1 / b) / b := by
    simp [leontiefDemand]
  have hdot : ∀ x : Fin 2 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := fun x => by
    simp [dotProduct, Fin.sum_univ_two]
  have haff : p ⬝ᵥ (leontiefDemand a b p w) = w := by
    rw [hdot, hx0, hx1]
    field_simp
  have e0 : a * (w / (p 0 / a + p 1 / b) / a) = w / (p 0 / a + p 1 / b) := by
    field_simp
  have e1 : b * (w / (p 0 / a + p 1 / b) / b) = w / (p 0 / a + p 1 / b) := by
    field_simp
  have hutil : leontief a b (leontiefDemand a b p w) = w / (p 0 / a + p 1 / b) := by
    simp [leontief, hx0, hx1, e0, e1]
  unfold IsMarshallianDemand budgetSet
  constructor
  · constructor
    · change ∀ i, 0 ≤ leontiefDemand a b p w i
      rw [Fin.forall_fin_two]
      constructor
      · rw [hx0]; exact div_nonneg ht0 (le_of_lt ha)
      · rw [hx1]; exact div_nonneg ht0 (le_of_lt hb)
    · rw [haff]
  · intro y hy
    obtain ⟨hyX, hyB⟩ := hy
    rw [hutil]
    unfold leontief
    apply (le_div_iff₀ hS0).mpr
    have hpa : 0 ≤ p 0 / a := le_of_lt (div_pos hp0 ha)
    have hpb : 0 ≤ p 1 / b := le_of_lt (div_pos hp1 hb)
    have h1 : min (a * y 0) (b * y 1) * (p 0 / a) ≤ (a * y 0) * (p 0 / a) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hpa
    have h2 : min (a * y 0) (b * y 1) * (p 1 / b) ≤ (b * y 1) * (p 1 / b) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hpb
    have g0 : (a * y 0) * (p 0 / a) = p 0 * y 0 := by
      field_simp
    have g1 : (b * y 1) * (p 1 / b) = p 1 * y 1 := by
      field_simp
    have hsum : min (a * y 0) (b * y 1) * (p 0 / a + p 1 / b)
        ≤ p 0 * y 0 + p 1 * y 1 := by
      calc min (a * y 0) (b * y 1) * (p 0 / a + p 1 / b)
          = min (a * y 0) (b * y 1) * (p 0 / a)
            + min (a * y 0) (b * y 1) * (p 1 / b) := by rw [mul_add]
        _ ≤ (a * y 0) * (p 0 / a) + (b * y 1) * (p 1 / b) := add_le_add h1 h2
        _ = p 0 * y 0 + p 1 * y 1 := by rw [g0, g1]
    have hyB' : p 0 * y 0 + p 1 * y 1 ≤ w := by
      rw [← hdot y]
      exact hyB
    exact le_trans hsum hyB'

/-- At the demanded kink bundle with positive wealth, the perfect-complements utility is not
differentiable, so no first-order condition is available there. -/
theorem not_differentiableAt_leontief_leontiefDemand {a b w : ℝ} {p : Fin 2 → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : ∀ i, 0 < p i) (hw : 0 < w) :
    ¬ DifferentiableAt ℝ (leontief a b) (leontiefDemand a b p w) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hp0 : 0 < p 0 := hp 0
  have hp1 : 0 < p 1 := hp 1
  have hS0 : 0 < p 0 / a + p 1 / b := add_pos (div_pos hp0 ha) (div_pos hp1 hb)
  have hS' : p 0 / a + p 1 / b ≠ 0 := ne_of_gt hS0
  have hx0 : leontiefDemand a b p w 0 = w / (p 0 / a + p 1 / b) / a := by
    simp [leontiefDemand]
  have hx1 : leontiefDemand a b p w 1 = w / (p 0 / a + p 1 / b) / b := by
    simp [leontiefDemand]
  have e0 : a * (w / (p 0 / a + p 1 / b) / a) = w / (p 0 / a + p 1 / b) := by
    field_simp
  have e1 : b * (w / (p 0 / a + p 1 / b) / b) = w / (p 0 / a + p 1 / b) := by
    field_simp
  have k0 : a * (leontiefDemand a b p w 0) = w / (p 0 / a + p 1 / b) := by
    rw [hx0]; exact e0
  have k1 : b * (leontiefDemand a b p w 1) = w / (p 0 / a + p 1 / b) := by
    rw [hx1]; exact e1
  set T : ℝ := w / (p 0 / a + p 1 / b) with hT
  set X : Fin 2 → ℝ := leontiefDemand a b p w with hX
  set E : Fin 2 → ℝ := Pi.single 0 1 with hE
  have _htpos : 0 < T := div_pos hw hS0
  have he0 : E 0 = 1 := by rw [hE]; exact Pi.single_eq_same _ _
  have he1 : E 1 = 0 := by rw [hE]; exact Pi.single_eq_of_ne (by decide) _
  have hc : DifferentiableAt ℝ (fun s : ℝ => X + s • E) 0 := by fun_prop
  have hc0 : (fun s : ℝ => X + s • E) 0 = X := by simp
  have hce0 : ∀ s : ℝ, (X + s • E) 0 = X 0 + s := fun s => by
    simp [Pi.add_apply, Pi.smul_apply, he0, smul_eq_mul]
  have hce1 : ∀ s : ℝ, (X + s • E) 1 = X 1 := fun s => by
    simp [Pi.add_apply, Pi.smul_apply, he1, smul_eq_mul]
  have arg0 : ∀ s : ℝ, a * (X 0 + s) = T + a * s := fun s => by rw [mul_add, k0]
  have hψ_eq : ∀ s : ℝ, (leontief a b ∘ fun s : ℝ => X + s • E) s
      = min (T + a * s) T := fun s => by
    simp only [Function.comp_apply, leontief, hce0 s, hce1 s, arg0 s, k1]
  intro hd
  have hd0 : DifferentiableAt ℝ (leontief a b) ((fun s : ℝ => X + s • E) 0) := by
    rw [hc0]; exact hd
  have hψ : DifferentiableAt ℝ (leontief a b ∘ fun s : ℝ => X + s • E) 0 :=
    DifferentiableAt.comp 0 hd0 hc
  have hM : HasDerivAt (leontief a b ∘ fun s : ℝ => X + s • E)
      (deriv (leontief a b ∘ fun s : ℝ => X + s • E) 0) 0 := hψ.hasDerivAt
  have hψ_right : ∀ s ∈ Set.Ici (0 : ℝ), (leontief a b ∘ fun s : ℝ => X + s • E) s
      = T := fun s hs => by
    rw [hψ_eq s]
    apply min_eq_right
    have hs0 : (0 : ℝ) ≤ s := Set.mem_Ici.mp hs
    have hmul : (0 : ℝ) ≤ a * s := mul_nonneg (le_of_lt ha) hs0
    linarith
  have hψ_left : ∀ s ∈ Set.Iic (0 : ℝ), (leontief a b ∘ fun s : ℝ => X + s • E) s
      = T + a * s := fun s hs => by
    rw [hψ_eq s]
    apply min_eq_left
    have hs0 : s ≤ (0 : ℝ) := Set.mem_Iic.mp hs
    have hmul : a * s ≤ (0 : ℝ) :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hs0
    linarith
  have hψ0_val : (leontief a b ∘ fun s : ℝ => X + s • E) 0 = T := by
    rw [hψ_eq 0, mul_zero, add_zero]; exact min_self T
  have heq_right : (leontief a b ∘ fun s : ℝ => X + s • E)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] (fun _ => T) := by
    apply eventually_nhdsWithin_of_forall
    intro s hs
    exact hψ_right s hs
  have hval_right : (leontief a b ∘ fun s : ℝ => X + s • E) 0 = (fun _ => T) 0 :=
    hψ0_val
  have hconst : HasDerivWithinAt (fun _ => T) 0 (Set.Ici (0 : ℝ)) 0 :=
    hasDerivWithinAt_const 0 (Set.Ici 0) T
  have hψ0 : HasDerivWithinAt (leontief a b ∘ fun s : ℝ => X + s • E) 0
      (Set.Ici (0 : ℝ)) 0 :=
    hconst.congr_of_eventuallyEq heq_right hval_right
  have hM_right : HasDerivWithinAt (leontief a b ∘ fun s : ℝ => X + s • E)
      (deriv (leontief a b ∘ fun s : ℝ => X + s • E) 0) (Set.Ici (0 : ℝ)) 0 :=
    hM.hasDerivWithinAt
  have hM0 : deriv (leontief a b ∘ fun s : ℝ => X + s • E) 0 = 0 :=
    UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici 0) hM_right hψ0
  have h1 : HasDerivAt (fun s : ℝ => a * s) a 0 := by
    have h := HasDerivAt.const_mul a (hasDerivAt_id (0 : ℝ))
    simpa using h
  have hlin : HasDerivAt (fun s : ℝ => T + a * s) a 0 :=
    HasDerivAt.const_add T h1
  have hlin_within : HasDerivWithinAt (fun s : ℝ => T + a * s) a (Set.Iic (0 : ℝ)) 0 :=
    hlin.hasDerivWithinAt
  have heq_left : (leontief a b ∘ fun s : ℝ => X + s • E)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Iic 0)] (fun s => T + a * s) := by
    apply eventually_nhdsWithin_of_forall
    intro s hs
    exact hψ_left s hs
  have hval_left : (leontief a b ∘ fun s : ℝ => X + s • E) 0
      = (fun s => T + a * s) 0 := by
    rw [hψ0_val]
    simp
  have hψa : HasDerivWithinAt (leontief a b ∘ fun s : ℝ => X + s • E) a
      (Set.Iic (0 : ℝ)) 0 :=
    hlin_within.congr_of_eventuallyEq heq_left hval_left
  have hM_left : HasDerivWithinAt (leontief a b ∘ fun s : ℝ => X + s • E)
      (deriv (leontief a b ∘ fun s : ℝ => X + s • E) 0) (Set.Iic (0 : ℝ)) 0 :=
    hM.hasDerivWithinAt
  have hMa : deriv (leontief a b ∘ fun s : ℝ => X + s • E) 0 = a :=
    UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic 0) hM_left hψa
  have hcontra : a = 0 := by rw [← hMa, hM0]
  exact (ne_of_gt ha) hcontra

end MathlibExt.Economics.Consumer
