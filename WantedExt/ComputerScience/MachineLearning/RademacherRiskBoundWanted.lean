/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.RademacherComplexity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Rademacher risk bound

Bartlett and Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural
results*, JMLR 3 (2002), Theorem 8: for a loss `L` and a dominating cost `φ ≥ L`, both with
values in `[0, 1]`, with probability at least `1 - δ` over an i.i.d. sample of size `n`, every
`f` in the class satisfies

`𝔼 L(Y, f(X)) ≤ (1/n) ∑ᵢ φ(Yᵢ, f(Xᵢ)) + (complexity term) + √(8 log (2/δ) / n)`.

The complexity term is stated here in the convention of
`Cslib.MachineLearning.Rademacher.rademacherComplexity` (no absolute value, normalization
`1/n`): it is `2 𝔼_S R(φ ∘ F|_S)`, the expected empirical Rademacher complexity of the cost
vectors `(φ(Yᵢ, f(Xᵢ)))ᵢ`. This is the quantity reached in the last display of Bartlett and
Mendelson's proof (`2 𝔼 sup_h (1/n) ∑ σᵢ h(Xᵢ, Yᵢ)`, page 468), and it is at most their
`R_n(φ̃ ∘ F)`; their recentring `φ̃ = φ(·, ·) - φ(·, 0)` is not needed because this
complexity is translation invariant (`rademacherComplexity_add_singleton`). The statement is
restricted to a finite class `F`, for which every quantity involved is measurable.
Shalev-Shwartz and Ben-David (*Understanding Machine Learning*, CUP 2014, Theorem 26.5, part 1)
state the case `φ = L` with the sharper deviation term `√(2 log (2/δ) / n)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Rademacher

open MeasureTheory

/-- The cost vectors `(φ(yᵢ, f(xᵢ)))ᵢ` of the functions `f ∈ F` on a sample
`S = ((x₁, y₁), …, (xₙ, yₙ))`. -/
def costVectors {X Y A : Type*} (φ : Y → A → ℝ) (F : Set (X → A)) {n : ℕ}
    (S : Fin n → X × Y) : Set (Fin n → ℝ) :=
  (fun f i => φ (S i).2 (f (S i).1)) '' F

/-- **The Rademacher risk bound** (Bartlett and Mendelson, *Rademacher and Gaussian
complexities: risk bounds and structural results*, JMLR 3, 2002, Theorem 8, in the
no-absolute-value convention and for a finite class): let `P` be a probability measure on
`X × Y`, let `L ≤ φ` be measurable along every `f ∈ F` with `0 ≤ L` and `φ ≤ 1`, and let
`0 < δ < 1`. Then with probability at least `1 - δ` over an i.i.d. sample `S ∼ Pⁿ`, every
`f ∈ F` satisfies
`𝔼_P L(Y, f(X)) ≤ (1/n) ∑ᵢ φ(Yᵢ, f(Xᵢ)) + 2 𝔼_{S'} R(φ ∘ F|_{S'}) + √(8 log (2/δ) / n)`
(for `φ = L` this is also Shalev-Shwartz and Ben-David, Theorem 26.5, part 1, with a weaker
constant). -/
theorem_wanted risk_le_empirical_add_rademacher {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (L φ : Y → A → ℝ) (hL : ∀ y a, 0 ≤ L y a) (hφ : ∀ y a, φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a) (F : Set (X → A)) (hF : F.Finite)
    (hmeasL : ∀ f ∈ F, Measurable fun z : X × Y => L z.2 (f z.1))
    (hmeasφ : ∀ f ∈ F, Measurable fun z : X × Y => φ z.2 (f z.1))
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => P)
      {S | ∀ f ∈ F, ∫ z, L z.2 (f z.1) ∂P ≤
        (n : ℝ)⁻¹ * ∑ i, φ (S i).2 (f (S i).1) +
          2 * ∫ S', rademacherComplexity (costVectors φ F S') ∂(Measure.pi fun _ : Fin n => P) +
          Real.sqrt (8 * Real.log (2 / δ) / n)}

end Cslib.MachineLearning.Rademacher
