/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalCurrying
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativePrisms

/-!
# The original fixed-base marked evaluation and its universal families

The actual maximal fixed-base mapping complex represents marked maps from
the maximally marked parameter product over the supplied original base.
The universal evaluation uses the original prism and has its literal base
equation. The inverse bijection retains every parameter simplex and both
native pullback projections. No parameter fibrancy or marked model
structure is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original marked parameter families with their literal whole-map base equation. -/
def RelativeMaxFamily (K : SSet.{u}) {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :=
  {f : prod (max K) X ⟶ Y // f ≫ p = prodSnd (max K) X ≫ r}

/-- Universal fixed-base evaluation reads the same complete original maximal marked prism. -/
def relativeEvaluation {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    prod (max (relativeMappingComplex .maximal r p)) X ⟶ Y :=
  maxUncurry (pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r))

/-- The universal original evaluation lies over the original source projection. -/
theorem relativeEvaluation_over {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeEvaluation r p ≫ p =
      prodSnd (max (relativeMappingComplex .maximal r p)) X ≫ r := by
  apply Hom.ext
  ext n z
  let f := (pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)).app n z.1
  let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ Y.toSSet := f.hom
  let t : (SSet.stdSimplex.obj n.unop ⊗ X.toSSet).obj n :=
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)), z.2)
  have h : F ≫ p.hom = CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom :=
    relativeMapping_prism_over .maximal r p n z.1
  exact ConcreteCategory.congr_hom (congr_app h n) t

/-- The original maximally marked family curries over the same actual base-map point. -/
theorem maxCurry_over {K : SSet.{u}} {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (f : prod (max K) X ⟶ Y)
    (hf : f ≫ p = prodSnd (max K) X ≫ r) :
    maxCurry f ≫ mappingComplexPost .maximal X p =
      SSet.stdSimplex.isTerminalObj₀.from K ≫ mappingBasePoint .maximal r := by
  ext n a
  apply Hom.ext
  let F : K ⊗ X.toSSet ⟶ Y.toSSet := f.hom
  have h : F ≫ p.hom = CartesianMonoidalCategory.snd K X.toSSet ≫ r.hom := congrArg Hom.hom hf
  change ((SSet.yonedaEquiv.symm a ▷ X.toSSet) ≫ F) ≫ p.hom =
    ((mappingBasePoint .maximal r).app n ((SSet.stdSimplex.isTerminalObj₀.from K).app n a)).hom
  rw [mappingBasePoint_app_hom, Category.assoc, h, ← Category.assoc]
  rfl

private theorem maxUncurry_relative_over {K : SSet.{u}} {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (g : K ⟶ relativeMappingComplex .maximal r p) :
    maxUncurry (g ≫ pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)) ≫ p =
      prodSnd (max K) X ≫ r := by
  let c : relativeMappingComplex .maximal r p ⟶ mappingComplex .maximal X Y :=
    pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)
  change maxUncurry (g ≫ c) ≫ p = _
  rw [maxUncurry_pre]
  let a : prod (max K) X ⟶ prod (max (relativeMappingComplex .maximal r p)) X :=
    prodMap (maximal.map g) (𝟙 X)
  let v : prod (max (relativeMappingComplex .maximal r p)) X ⟶ Y := maxUncurry c
  have hv : v ≫ p = prodSnd (max (relativeMappingComplex .maximal r p)) X ≫ r :=
    relativeEvaluation_over r p
  change (a ≫ v) ≫ p = prodSnd (max K) X ≫ r
  rw [Category.assoc, hv, ← Category.assoc]
  apply Hom.ext
  rfl

/-- The native maximal fixed-base complex represents all original maximally marked parameter families. -/
def relativeMaxFamilyEquiv (K : SSet.{u}) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    RelativeMaxFamily K r p ≃ (K ⟶ relativeMappingComplex .maximal r p) where
  toFun f := pullback.lift (maxCurry f.val) (SSet.stdSimplex.isTerminalObj₀.from K)
    (maxCurry_over r p f.val f.property)
  invFun g := ⟨maxUncurry (g ≫
    pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)),
      maxUncurry_relative_over r p g⟩
  left_inv f := by
    apply Subtype.ext
    change maxUncurry (pullback.lift (maxCurry f.val) (SSet.stdSimplex.isTerminalObj₀.from K)
      (maxCurry_over r p f.val f.property) ≫
        pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)) = f.val
    rw [pullback.lift_fst]
    exact maxUncurry_maxCurry f.val
  right_inv g := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact maxCurry_maxUncurry _
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Universal evaluation corresponds to the identity of the same original fixed-base mapping complex. -/
theorem relativeMaxFamilyEquiv_evaluation {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMaxFamilyEquiv (relativeMappingComplex .maximal r p) r p
      ⟨relativeEvaluation r p, relativeEvaluation_over r p⟩ = 𝟙 _ := by
  let q := relativeMaxFamilyEquiv (relativeMappingComplex .maximal r p) r p
  let f : RelativeMaxFamily (relativeMappingComplex .maximal r p) r p :=
    ⟨relativeEvaluation r p, relativeEvaluation_over r p⟩
  change q f = 𝟙 _
  apply q.symm.injective
  have h : q.symm (𝟙 _) = f := by
    apply Subtype.ext
    let c : relativeMappingComplex .maximal r p ⟶ mappingComplex .maximal X Y :=
      pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)
    change maxUncurry (𝟙 _ ≫ c) = maxUncurry c
    rw [Category.id_comp]
  exact (q.symm_apply_apply f).trans h.symm

/-- The original parameter map is retained by the represented evaluation family. -/
theorem relativeMaxFamilyEquiv_symm_pre {K K' : SSet.{u}} {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (a : K' ⟶ K) (g : K ⟶ relativeMappingComplex .maximal r p) :
    ((relativeMaxFamilyEquiv K' r p).symm (a ≫ g)).val =
      prodMap (maximal.map a) (𝟙 X) ≫ ((relativeMaxFamilyEquiv K r p).symm g).val := by
  let c : relativeMappingComplex .maximal r p ⟶ mappingComplex .maximal X Y :=
    pullback.fst (mappingComplexPost .maximal X p) (mappingBasePoint .maximal r)
  change maxUncurry ((a ≫ g) ≫ c) = prodMap (maximal.map a) (𝟙 X) ≫ maxUncurry (g ≫ c)
  rw [Category.assoc, maxUncurry_pre]

end SSet.Marked
