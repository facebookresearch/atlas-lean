/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import MathlibExt.Algebra.Homology.CochainGradedPairingConnector
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality

/-!
# Connecting morphisms and group-cohomology cups

Let `G` be a group, `k` a commutative ring, and `S : 0 → S₁ → S₂ → S₃ → 0` a short exact
sequence of representations. If `A ⊗ S` is short exact, the right connecting map satisfies `x
∪ δ_S(y) = (-1)^p δ_{A⊗S}(x ∪ y)` for `x ∈ H^p(G,A)` and `y ∈ H^q(G,S₃)`. If `S ⊗ B` is short
exact, the left law is `δ_S(x) ∪ y = δ_{S⊗B}(x ∪ y)` for `x ∈ H^p(G,S₃)` and `y ∈ H^q(G,B)`.

Both identities use the canonical homology identifications of `p + (q + 1)` or `(p + 1) + q`
with `p + q + 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Let `k` be a commutative ring, `G` a group, `A : Rep k G`, and `S : 0 → S₁ → S₂ → S₃ → 0`
short exact. Assume `A ⊗ S` is short exact. For `p,q : ℕ`, `(𝟙 ⊗ δ_S^q) ≫ cup_{p,q+1} ≫ e =
(-1)^p • (cup_{p,q} ≫ δ_{A⊗S}^{p+q})` as maps `H^p(G,A) ⊗ H^q(G,S₃) → H^{p+q+1}(G,A ⊗ S₁)`.
Here the first cup has coefficients `A,S₁`, the second `A,S₃`, and `e` identifies `p + (q +
1)` with `p + q + 1`. -/
theorem cup_delta_right
    (A : Rep k G) (S : ShortComplex (Rep k G))
    (hS : S.ShortExact)
    (hAS : (S.map (tensorLeft A)).ShortExact)
    (p q : ℕ) :
    ((𝟙 (groupCohomology A p) ⊗ₘ δ hS q (q + 1) rfl) ≫
        cup G k A S.X₁ p (q + 1) ≫
        ((inhomogeneousCochains (A ⊗ S.X₁)).homologyIsoOfEq
          (show p + (q + 1) = p + q + 1 by omega)).hom) =
      ((-1 : ℤ) ^ p) •
        (cup G k A S.X₃ p q ≫
          δ hAS (p + q) (p + q + 1) rfl) := by
  set_option backward.isDefEq.respectTransparency false in
  apply HomologicalComplex.CochainGradedPairing.pairHomology_delta_right k
    (map_cochainsFunctor_shortExact hS)
    (map_cochainsFunctor_shortExact hAS)
    (inhomogeneousCupPairing G k A S.X₁)
    (inhomogeneousCupPairing G k A S.X₂)
    (inhomogeneousCupPairing G k A S.X₃)
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := 𝟙 A) (g := S.f) i j
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := 𝟙 A) (g := S.g) i j

/-- Let `k` be a commutative ring, `G` a group, `B : Rep k G`, and `S : 0 → S₁ → S₂ → S₃ → 0`
short exact. Assume `S ⊗ B` is short exact. For `p,q : ℕ`, `(δ_S^p ⊗ 𝟙) ≫ cup_{p+1,q} ≫ e =
cup_{p,q} ≫ δ_{S⊗B}^{p+q}` as maps `H^p(G,S₃) ⊗ H^q(G,B) → H^{p+q+1}(G,S₁ ⊗ B)`. The cups have
coefficients `S₁,B` and `S₃,B`, respectively, and `e` identifies `(p + 1) + q` with `p + q +
1`. -/
theorem cup_delta_left
    (B : Rep k G) (S : ShortComplex (Rep k G))
    (hS : S.ShortExact)
    (hSB : (S.map (tensorRight B)).ShortExact)
    (p q : ℕ) :
    ((δ hS p (p + 1) rfl ⊗ₘ 𝟙 (groupCohomology B q)) ≫
        cup G k S.X₁ B (p + 1) q ≫
        ((inhomogeneousCochains (S.X₁ ⊗ B)).homologyIsoOfEq
          (show (p + 1) + q = p + q + 1 by omega)).hom) =
      cup G k S.X₃ B p q ≫
        δ hSB (p + q) (p + q + 1) rfl := by
  set_option backward.isDefEq.respectTransparency false in
  apply HomologicalComplex.CochainGradedPairing.pairHomology_delta_left k
    (map_cochainsFunctor_shortExact hS)
    (map_cochainsFunctor_shortExact hSB)
    (inhomogeneousCupPairing G k S.X₁ B)
    (inhomogeneousCupPairing G k S.X₂ B)
    (inhomogeneousCupPairing G k S.X₃ B)
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := S.f) (g := 𝟙 B) i j
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := S.g) (g := 𝟙 B) i j

end groupCohomology
