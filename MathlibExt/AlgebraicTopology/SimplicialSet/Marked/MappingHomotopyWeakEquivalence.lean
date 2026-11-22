/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalMappingHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence

/-!
# Original marked interval contractions give mapping weak equivalences

A strict original section and a whole maximally marked interval
contraction give actual simplicial homotopy inverses on the same maximal
mapping complexes. When those actual complexes are Kan, the existing
native homotopy theorem gives the realization weak equivalence. No
marked-model structure or comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- A strict original section and its actual maximal marked contraction induce the genuine mapping weak equivalence. -/
theorem mappingComplexPre_realizationWeakEquivalence_of_contraction {P Q Y : Marked.{u}}
    (f : P ⟶ Q) (g : Q ⟶ P) (hfg : f ≫ g = 𝟙 P)
    (H : prod (max (Δ[1] : SSet.{u})) Q ⟶ Q)
    (h₀ : prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 Q) ≫ H =
      (zeroParameterUnitIso .maximal Q).hom ≫ (g ≫ f))
    (h₁ : prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 Q) ≫ H =
      (zeroParameterUnitIso .maximal Q).hom ≫ 𝟙 Q)
    [KanComplex (mappingComplex .maximal P Y)] [KanComplex (mappingComplex .maximal Q Y)] :
    realizationWeakEquivalences (mappingComplexPre .maximal f Y) := by
  let F : mappingComplex .maximal Q Y ⟶ mappingComplex .maximal P Y := mappingComplexPre .maximal f Y
  let G : mappingComplex .maximal P Y ⟶ mappingComplex .maximal Q Y := mappingComplexPre .maximal g Y
  have hF : mappingComplexPre .maximal (g ≫ f) Y = F ≫ G := mappingComplexPre_comp .maximal g f Y
  have hId : mappingComplexPre .maximal (𝟙 Q) Y = 𝟙 (mappingComplex .maximal Q Y) :=
    mappingComplexPre_id .maximal Q Y
  let HX : SSet.Homotopy (F ≫ G) (𝟙 (mappingComplex .maximal Q Y)) :=
    hF ▸ hId ▸ maximalMappingPreHomotopy Y (g ≫ f) (𝟙 Q) H h₀ h₁
  have hGF : G ≫ F = 𝟙 (mappingComplex .maximal P Y) :=
    (mappingComplexPre_comp .maximal f g Y).symm.trans
      ((congrArg (fun q => mappingComplexPre .maximal q Y) hfg).trans (mappingComplexPre_id .maximal P Y))
  let HY : SSet.Homotopy (G ≫ F) (𝟙 (mappingComplex .maximal P Y)) :=
    SSet.RelativeMorphism.Homotopy.ofEq
      (congrArg (fun q => SSet.RelativeMorphism.botEquiv.symm q) hGF)
  exact (KanComplex.W_iff_realizationWeakEquivalence F).mp (KanComplex.W.of_homotopy F G HX HY)

end SSet.Marked
