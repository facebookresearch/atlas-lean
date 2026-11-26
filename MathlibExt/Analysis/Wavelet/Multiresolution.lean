/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Multiresolution approximations of `L²(ℝ)`

S. Mallat's definition (*Multiresolution approximations and wavelet orthonormal bases of
`L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), 69–87, Definition, properties (1)–(5)): a
multiresolution approximation of `L²(ℝ)` is a sequence `(V_j)_{j ∈ ℤ}` of closed subspaces with

1. `V_j ⊂ V_{j+1}`;
2. `⋃_j V_j` dense in `L²(ℝ)` and `⋂_j V_j = {0}`;
3. `f(x) ∈ V_j ⟺ f(2x) ∈ V_{j+1}`;
4. `f(x) ∈ V_j ⟹ f(x - 2^{-j} k) ∈ V_j` for `k ∈ ℤ`;
5. an isomorphism `I : V_0 → ℓ²(ℤ)` which commutes with the action of `ℤ` (integer
   translations of functions and shifts of sequences).

Resolution increases with `j` in this convention (`V_j ⊂ V_{j+1}`); texts that index the spaces
by the scale `2^j` instead write `V_{j+1} ⊂ V_j`. Functions are elements of the complex `L²(ℝ)`, and
a dilated or translated function is described by any `L²` element almost everywhere equal to it.
The main theorems of the paper (an orthonormal basis of integer translates of a scaling
function, and the wavelet orthonormal basis) are proved in
`MathlibExt.Analysis.Wavelet.ScalingFunction` and
`MathlibExt.Analysis.Wavelet.WaveletBasis`.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.Wavelet.Multiresolution

/-- **Multiresolution approximation of `L²(ℝ)`** (S. Mallat, *Multiresolution approximations
and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), Definition,
properties (1)–(5)). A sequence `V : ℤ → Submodule ℂ (L²(ℝ))` of closed subspaces is a
multiresolution approximation if
(1) `V j ≤ V (j + 1)`;
(2) `⋃ⱼ V j` is dense and `⋂ⱼ V j = {0}`;
(3) for `g` a.e. equal to `x ↦ f (2x)`, `f ∈ V j ↔ g ∈ V (j + 1)`;
(4) for `g` a.e. equal to `x ↦ f (x - 2^{-j} k)` with `k ∈ ℤ`, `f ∈ V j → g ∈ V j`;
(5) there is a continuous linear isomorphism `I : V 0 ≃ ℓ²(ℤ)` commuting with the action of
`ℤ`: if `g` is a.e. equal to `x ↦ f (x - k)` then `I g n = I f (n - k)`. -/
def IsMultiresolutionApproximation (V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    Prop :=
  (∀ j, IsClosed (V j : Set (Lp ℂ 2 (volume : Measure ℝ)))) ∧
  (∀ j, V j ≤ V (j + 1)) ∧
  Dense (⋃ j, (V j : Set (Lp ℂ 2 (volume : Measure ℝ)))) ∧
  (∀ f : Lp ℂ 2 (volume : Measure ℝ), (∀ j, f ∈ V j) → f = 0) ∧
  (∀ (j : ℤ) (f g : Lp ℂ 2 (volume : Measure ℝ)),
    (⇑g =ᵐ[volume] fun x => f (2 * x)) → (f ∈ V j ↔ g ∈ V (j + 1))) ∧
  (∀ (j k : ℤ) (f g : Lp ℂ 2 (volume : Measure ℝ)),
    (⇑g =ᵐ[volume] fun x => f (x - (2 : ℝ) ^ (-j) * k)) → f ∈ V j → g ∈ V j) ∧
  ∃ I : V 0 ≃L[ℂ] lp (fun _ : ℤ => ℂ) 2,
    ∀ (k : ℤ) (f g : V 0),
      (⇑(g : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
          fun x => (f : Lp ℂ 2 (volume : Measure ℝ)) (x - k)) →
        ∀ n : ℤ, I g n = I f (n - k)

end MathlibExt.Analysis.Wavelet.Multiresolution
