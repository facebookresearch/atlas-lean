/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBead
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoStandardBeadPushout

/-!
# Gluing both complete original coherent bead coefficients

The full coefficient maps are the original prefix and suffix direct
images, with the original pivot endpoint equations. Composition is the
same native union of every original flag, in every scalar degree.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.CoefficientGluing

open SimplicialEnrichment
open SSet.OriginalTwoBead.OrdinalCharts

/-- The original zero-to-last full Hom of a bead. -/
abbrev beadHom (n : ℕ) : SSet.{u} :=
  nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1)))
    (ULift.up.{u} (Fin.last n)))

/-- The same original pivot object in the combined coherent simplex. -/
def middle (p q : ℕ) : coherentSimplex.{u} ⦋p + q⦌ :=
  SimplicialThickening.mk (ULift.up (pivot p q))

/-- The actual original initial-prefix endpoint equation. -/
theorem prefix_first (p q : ℕ) :
    (prefixOperator p q).toOrderHom.uliftMap (ULift.up.{u} 0) = ULift.up.{u} 0 :=
  ULift.ext (prefix_zero p q)

/-- The actual original terminal-prefix endpoint equation. -/
theorem prefix_final (p q : ℕ) :
    (prefixOperator p q).toOrderHom.uliftMap (ULift.up.{u} (Fin.last p)) =
      ULift.up.{u} (pivot p q) :=
  ULift.ext (prefix_last p q)

/-- The actual original initial-suffix endpoint equation. -/
theorem suffix_first (p q : ℕ) :
    (suffixOperator p q).toOrderHom.uliftMap (ULift.up.{u} 0) =
      ULift.up.{u} (pivot p q) :=
  ULift.ext (suffix_zero p q)

/-- The actual original terminal-suffix endpoint equation. -/
theorem suffix_final (p q : ℕ) :
    (suffixOperator p q).toOrderHom.uliftMap (ULift.up.{u} (Fin.last q)) =
      ULift.up.{u} (Fin.last (p + q)) :=
  ULift.ext (suffix_last p q)

/-- The full first coefficient direct image with the same original pivot. -/
def leftFunctor (p q : ℕ) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (p + 1))) (ULift.up (Fin.last p)) ⥤
      SimplicialThickening.Path (ULift.up.{u} (0 : Fin (p + q + 1)))
        (ULift.up (pivot p q)) :=
  SimplicialThickening.functorMap (prefixOperator p q).toOrderHom.uliftMap
      (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (p + 1))))
      (SimplicialThickening.mk (ULift.up.{u} (Fin.last p))) ⋙
    PathEndpointTransport.retarget (prefix_first p q) (prefix_final p q)

/-- The full second coefficient direct image with the same original pivot. -/
def rightFunctor (p q : ℕ) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (q + 1))) (ULift.up (Fin.last q)) ⥤
      SimplicialThickening.Path (ULift.up.{u} (pivot p q))
        (ULift.up (Fin.last (p + q))) :=
  SimplicialThickening.functorMap (suffixOperator p q).toOrderHom.uliftMap
      (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (q + 1))))
      (SimplicialThickening.mk (ULift.up.{u} (Fin.last q))) ⋙
    PathEndpointTransport.retarget (suffix_first p q) (suffix_final p q)

/-- The entire original first-bead Hom map. -/
def leftMap (p q : ℕ) :
    beadHom.{u} p ⟶ nerve
      (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (p + q + 1)))
        (ULift.up.{u} (pivot p q))) :=
  nerveMap (leftFunctor p q)

/-- The entire original second-bead Hom map. -/
def rightMap (p q : ℕ) :
    beadHom.{u} q ⟶ nerve
      (SimplicialThickening.Path (ULift.up.{u} (pivot p q))
        (ULift.up.{u} (Fin.last (p + q)))) :=
  nerveMap (rightFunctor p q)

/-- The first full coefficient is the actual original prefix Hom map and endpoint transport. -/
theorem leftMap_original (p q : ℕ) :
    leftMap.{u} p q =
      (coherentSimplexMap (prefixOperator p q)).map (initial p) (terminal p) ≫
        eqToHom (congrArg₂
          (fun a b : ULift.{u} (Fin (p + q + 1)) => nerve (SimplicialThickening.Path a b))
          (prefix_first p q) (prefix_final p q)) := by
  change nerveMap
      (SimplicialThickening.functorMap (prefixOperator p q).toOrderHom.uliftMap
        (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (p + 1))))
        (SimplicialThickening.mk (ULift.up.{u} (Fin.last p)))) ≫
    nerveMap (PathEndpointTransport.retarget (prefix_first p q) (prefix_final p q)) = _
  exact congrArg (fun f =>
    (coherentSimplexMap (prefixOperator p q)).map (initial p) (terminal p) ≫ f)
      (PathEndpointTransport.nerve_retarget (prefix_first p q) (prefix_final p q))

/-- The second full coefficient is the actual original suffix Hom map and endpoint transport. -/
theorem rightMap_original (p q : ℕ) :
    rightMap.{u} p q =
      (coherentSimplexMap (suffixOperator p q)).map (initial q) (terminal q) ≫
        eqToHom (congrArg₂
          (fun a b : ULift.{u} (Fin (p + q + 1)) => nerve (SimplicialThickening.Path a b))
          (suffix_first p q) (suffix_final p q)) := by
  change nerveMap
      (SimplicialThickening.functorMap (suffixOperator p q).toOrderHom.uliftMap
        (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (q + 1))))
        (SimplicialThickening.mk (ULift.up.{u} (Fin.last q)))) ≫
    nerveMap (PathEndpointTransport.retarget (suffix_first p q) (suffix_final p q)) = _
  exact congrArg (fun f =>
    (coherentSimplexMap (suffixOperator p q)).map (initial q) (terminal q) ≫ f)
      (PathEndpointTransport.nerve_retarget (suffix_first p q) (suffix_final p q))

/-- Compose the entire two original Hom coefficients by the original union. -/
def map (p q : ℕ) : beadHom.{u} p ⊗ beadHom.{u} q ⟶ beadHom.{u} (p + q) :=
  (leftMap p q ⊗ₘ rightMap p q) ≫
    eComp SSet.{u} (initial (p + q)) (middle p q) (terminal (p + q))

/-- Every flag is precisely the union of its two full original ordinal images. -/
theorem map_flags (p q m : ℕ) (a : beadHom.{u} p _⦋m⦌) (b : beadHom.{u} q _⦋m⦌)
    (t : Fin (m + 1)) :
    (((map p q).app (op ⦋m⦌) (a, b)).obj t).I =
      (prefixOperator p q).toOrderHom.uliftMap '' (a.obj t).I ∪
        (suffixOperator p q).toOrderHom.uliftMap '' (b.obj t).I := rfl

/-- All original scalar operators act on both whole coefficients before their gluing. -/
theorem map_operator (p q : ℕ) {d e : SimplexCategoryᵒᵖ} (θ : d ⟶ e)
    (a : (beadHom.{u} p).obj d) (b : (beadHom.{u} q).obj d) :
    (beadHom (p + q)).map θ ((map p q).app d (a, b)) =
      (map p q).app e ((beadHom p).map θ a, (beadHom q).map θ b) :=
  rfl

end CategoryTheory.CoherentRealization.OriginalBead.CoefficientGluing
