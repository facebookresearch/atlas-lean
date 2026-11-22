/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import Mathlib.Tactic.FinCases
import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpineFibres

/-!
# Original ambient-prefix edge restrictions

The model-free induction uses the actual prefix pullback;
no caller preservation, cocone, gluing Iso or homotopical outcome is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace SimplicialSpace.FixedTupleSpinePrefix

private theorem edgeInclusion_ι (n r : ℕ) (h : r ≤ n) (i : Fin r) :
    edgeInclusion.{u} n r h i ≫ (SSet.Rezk.spinePrefixSubcomplex.{u} n r h).ι =
      SSet.Rezk.segalSpineEdgeMap n ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  rfl


private theorem edgeInclusion_adjacent (n r : ℕ) (h : r ≤ n)
    (j : ℕ) (hj : j + 1 < r) :
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
        edgeInclusion.{u} n r h ⟨j, by omega⟩ =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        edgeInclusion n r h ⟨j + 1, hj⟩ := by
  apply (cancel_mono (SSet.Rezk.spinePrefixSubcomplex.{u} n r h).ι).mp
  rw [Category.assoc, edgeInclusion_ι, Category.assoc, edgeInclusion_ι]
  unfold SSet.Rezk.segalSpineEdgeMap
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp,
    SimplexCategory.δ_zero_mkOfSucc, SimplexCategory.δ_one_mkOfSucc]
  congr 1


/-- The original prefix edge restrictions satisfy all literal adjacent endpoint equations. -/
theorem edgeProjection_adjacent (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n)
    (j : ℕ) (hj : j + 1 < r) :
    edgeProjection W n r h ⟨j, by omega⟩ ≫ W.diagram.δ (0 : Fin 2) =
      edgeProjection W n r h ⟨j + 1, hj⟩ ≫ W.diagram.δ (1 : Fin 2) := by
  unfold edgeProjection
  simp only [SimplicialObject.δ_def]
  rw [Category.assoc, ← discreteYonedaIso_naturality_index,
    ← Category.assoc, ← Functor.map_comp, ← op_comp]
  rw [Category.assoc, ← discreteYonedaIso_naturality_index,
    ← Category.assoc, ← Functor.map_comp, ← op_comp]
  rw [edgeInclusion_adjacent]


/-- Every original prefix vertex is the first source or a selected edge target. -/
def vertexProjection (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) : Fin (r + 1) →
      (prefixObject W n r h ⟶ W.diagram _⦋0⦌) :=
  Fin.cases
    (edgeProjection W n r h ⟨0, hr⟩ ≫ W.diagram.δ (1 : Fin 2))
    (fun i => edgeProjection W n r h i ≫ W.diagram.δ (0 : Fin 2))


/-- The target of each original edge is precisely its selected tuple successor vertex. -/
theorem edgeProjection_target (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) (i : Fin r) :
    edgeProjection W n r h i ≫ W.diagram.δ (0 : Fin 2) =
      vertexProjection W n r h hr i.succ := rfl


/-- The source of each original edge is precisely its selected tuple predecessor vertex. -/
theorem edgeProjection_source (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r) (i : Fin r) :
    edgeProjection W n r h i ≫ W.diagram.δ (1 : Fin 2) =
      vertexProjection W n r h hr i.castSucc := by
  by_cases hi : i.val = 0
  · have hi0 : i = (⟨0, hr⟩ : Fin r) := Fin.ext hi
    subst i
    rfl
  · have hpos : 1 ≤ i.val := by omega
    have hj : i.val - 1 + 1 < r := by omega
    have cast_eq : i.castSucc = (⟨i.val - 1, by omega⟩ : Fin r).succ := by
      apply Fin.ext
      dsimp
      omega
    rw [cast_eq]
    dsimp only [vertexProjection]
    have heq : (⟨i.val - 1 + 1, hj⟩ : Fin r) = i := by
      apply Fin.ext
      dsimp
      omega
    simpa only [heq, Fin.cases_succ] using
      (edgeProjection_adjacent W n r h (i.val - 1) hj).symm



end SimplicialSpace.FixedTupleSpinePrefix

namespace SimplicialSpace.FixedTupleSpineBoundary
section Generic
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- A binary product is compared to the actual chosen Fin2 product by both projections. -/
def binaryFinTwoIso (X : C) : X ⨯ X ≅ ∏ᶜ (fun _ : Fin 2 => X) where
  hom := Pi.lift (fun i => if i = 0 then prod.fst else prod.snd)
  inv := prod.lift (Pi.π _ (0 : Fin 2)) (Pi.π _ (1 : Fin 2))
  hom_inv_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Pi.lift_comp_π, Category.id_comp]
      simp
    · simp only [Category.assoc, prod.lift_snd, Pi.lift_comp_π,
        if_neg (by decide : (1 : Fin 2) ≠ 0), Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    fin_cases i <;> simp [Category.assoc]


/-- The forward Fin2 projections retain both original binary projections. -/
theorem binaryFinTwoIso_hom_legs (X : C) :
    (binaryFinTwoIso X).hom ≫ Pi.π _ (0 : Fin 2) = prod.fst ∧
    (binaryFinTwoIso X).hom ≫ Pi.π _ (1 : Fin 2) = prod.snd := by
  constructor <;> simp [binaryFinTwoIso]


/-- The inverse retains both selected Fin2 projections. -/
theorem binaryFinTwoIso_inv_legs (X : C) :
    (binaryFinTwoIso X).inv ≫ prod.fst = Pi.π _ (0 : Fin 2) ∧
    (binaryFinTwoIso X).inv ≫ prod.snd = Pi.π _ (1 : Fin 2) := by
  exact ⟨prod.lift_fst _ _, prod.lift_snd _ _⟩


/-- Changing the base by an actual Iso preserves the chosen pullback and BOTH legs. -/
def pullbackPostIso {X Y Z Z' : C} (f : X ⟶ Z) (g : Y ⟶ Z) (e : Z ≅ Z') :
    pullback (f ≫ e.hom) (g ≫ e.hom) ≅ pullback f g where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono e.hom).mp (by simpa only [Category.assoc] using
      (pullback.condition (f := f ≫ e.hom) (g := g ≫ e.hom))))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    (by simpa only [Category.assoc] using
      congrArg (fun q => q ≫ e.hom) (pullback.condition (f := f) (g := g)))
  hom_inv_id := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
      pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
      pullback.lift_snd, Category.id_comp]


/-- The base-Iso comparison leaves both original pullback projections unchanged. -/
theorem pullbackPostIso_legs {X Y Z Z' : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) (e : Z ≅ Z') :
    (pullbackPostIso f g e).hom ≫ pullback.fst f g = pullback.fst _ _ ∧
    (pullbackPostIso f g e).hom ≫ pullback.snd f g = pullback.snd _ _ ∧
    (pullbackPostIso f g e).inv ≫ pullback.fst (f ≫ e.hom) (g ≫ e.hom) =
        pullback.fst _ _ ∧
    (pullbackPostIso f g e).inv ≫ pullback.snd (f ≫ e.hom) (g ≫ e.hom) =
        pullback.snd _ _ := by
  exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩


/-- The chosen product over Fin0 is proved terminal by its universal property. -/
def emptyProductIsTerminal (f : Fin 0 → C) : IsTerminal (∏ᶜ f) :=
  IsTerminal.ofUniqueHom
    (fun X => Pi.lift (fun i => Fin.elim0 i))
    (by
      intro X q
      apply Pi.hom_ext
      intro i
      exact Fin.elim0 i)


/-- Pulling back the identity along an original point gives that point source. -/
def identityPointPullbackIso {X Y : C} (p : Y ⟶ X) :
    pullback (𝟙 X) p ≅ Y where
  hom := pullback.snd _ _
  inv := pullback.lift p (𝟙 Y) (by simp only [Category.comp_id, Category.id_comp])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa only [Category.comp_id] using
        (pullback.condition (f := 𝟙 X) (g := p)).symm
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id,
        Category.id_comp]
  inv_hom_id := by
    simp only [pullback.lift_snd]


end Generic

end SimplicialSpace.FixedTupleSpineBoundary

namespace SimplicialSpace.FixedTupleSpineBoundary

/-- The one-edge tuple point has the actual ordered source and target vertices. -/
def oneEdgePoint (W : SimplicialSpace.{u})
    (x : Fin 2 → (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ ∏ᶜ (fun _ : Fin 2 => W.diagram _⦋0⦌) :=
  Pi.lift (fun i => SSet.yonedaEquiv.symm (x i))


/-- The exact Fin2 tuple point is the original binary pair point followed by the same Iso. -/
theorem oneEdgePoint_eq (W : SimplicialSpace.{u})
    (x : Fin 2 → (W.diagram _⦋0⦌) _⦋0⦌) :
    oneEdgePoint W x = mappingPointPair W (x 0) (x 1) ≫
      (binaryFinTwoIso (W.diagram _⦋0⦌)).hom := by
  apply Pi.hom_ext
  intro i
  fin_cases i
  · simp only [oneEdgePoint, Pi.lift_comp_π]
    change SSet.yonedaEquiv.symm (x 0) = mappingPointPair W (x 0) (x 1) ≫
      (binaryFinTwoIso (W.diagram _⦋0⦌)).hom ≫ Pi.π _ (0 : Fin 2)
    rw [(binaryFinTwoIso_hom_legs (W.diagram _⦋0⦌)).1, mappingPointPair_fst]
  · simp only [oneEdgePoint, Pi.lift_comp_π]
    change SSet.yonedaEquiv.symm (x 1) = mappingPointPair W (x 0) (x 1) ≫
      (binaryFinTwoIso (W.diagram _⦋0⦌)).hom ≫ Pi.π _ (1 : Fin 2)
    rw [(binaryFinTwoIso_hom_legs (W.diagram _⦋0⦌)).2, mappingPointPair_snd]


/-- The original one-edge all-vertex pullback, with its literal Fin2 base. -/
def oneEdgeTupleFibre (W : SimplicialSpace.{u})
    (x : Fin 2 → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (mappingEndpoint W ≫ (binaryFinTwoIso (W.diagram _⦋0⦌)).hom)
    (oneEdgePoint W x)


/-- The one-edge tuple fibre compares to the ORIGINAL chosen mapping fibre. -/
def oneEdgeTupleFibreIso (W : SimplicialSpace.{u})
    (x : Fin 2 → (W.diagram _⦋0⦌) _⦋0⦌) :
    oneEdgeTupleFibre W x ≅ mappingFibre W (x 0) (x 1) := by
  dsimp only [oneEdgeTupleFibre]
  exact pullback.congrHom rfl (oneEdgePoint_eq W x) ≪≫
    pullbackPostIso (mappingEndpoint W) (mappingPointPair W (x 0) (x 1))
      (binaryFinTwoIso (W.diagram _⦋0⦌))


/-- The k1 result includes the actual chosen product over its ONE edge. -/
def oneEdgeTupleFibreProductIso (W : SimplicialSpace.{u})
    (x : Fin 2 → (W.diagram _⦋0⦌) _⦋0⦌) :
    oneEdgeTupleFibre W x ≅ ∏ᶜ (fun _ : Fin 1 => mappingFibre W (x 0) (x 1)) :=
  oneEdgeTupleFibreIso W x ≪≫
    (productUniqueIso (fun _ : Fin 1 => mappingFibre W (x 0) (x 1))).symm


/-- The zero-edge fibre is built from A0 and its actual original vertex point. -/
def zeroEdgeTupleFibre (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (𝟙 (W.diagram _⦋0⦌)) (SSet.yonedaEquiv.symm x)


/-- The zero-edge original fibre is the actual Delta0, not the empty raw spine. -/
def zeroEdgeTupleFibreIso (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) : zeroEdgeTupleFibre W x ≅ (Δ[0] : SSet.{u}) :=
  identityPointPullbackIso (SSet.yonedaEquiv.symm x)


set_option linter.unusedVariables false in
/-- The zero-edge fibre compares to its actual empty product through terminality. -/
def zeroEdgeTupleFibreProductIso (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    zeroEdgeTupleFibre W x ≅ ∏ᶜ (fun i : Fin 0 => mappingFibre W x x) :=
  zeroEdgeTupleFibreIso W x ≪≫
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso (emptyProductIsTerminal _)



/-- The actual zero-edge all-vertex map lands in the chosen one-vertex product. -/
def zeroEdgeVertexMap (W : SimplicialSpace.{u}) :
    W.diagram _⦋0⦌ ⟶ ∏ᶜ (fun _ : Fin 1 => W.diagram _⦋0⦌) :=
  Pi.lift (fun _ => 𝟙 _)


/-- The actual zero-edge tuple point uses its same selected original vertex. -/
def zeroEdgePoint (W : SimplicialSpace.{u})
    (x : Fin 1 → (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ ∏ᶜ (fun _ : Fin 1 => W.diagram _⦋0⦌) :=
  Pi.lift (fun i => SSet.yonedaEquiv.symm (x i))


/-- The actual one-vertex map is the inverse of the chosen one-factor product Iso. -/
theorem zeroEdgeVertexMap_eq (W : SimplicialSpace.{u}) :
    zeroEdgeVertexMap W =
      (productUniqueIso (fun _ : Fin 1 => W.diagram _⦋0⦌)).inv := by
  apply Pi.hom_ext
  intro i
  simp only [zeroEdgeVertexMap, Pi.lift_comp_π, productUniqueIso_inv_π]
  simp


/-- The actual zero-edge tuple point transports the same original vertex through that Iso. -/
theorem zeroEdgePoint_eq (W : SimplicialSpace.{u})
    (x : Fin 1 → (W.diagram _⦋0⦌) _⦋0⦌) :
    zeroEdgePoint W x = SSet.yonedaEquiv.symm (x 0) ≫
      (productUniqueIso (fun _ : Fin 1 => W.diagram _⦋0⦌)).inv := by
  apply Pi.hom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp only [zeroEdgePoint, Pi.lift_comp_π, Category.assoc,
    productUniqueIso_inv_π]
  simp


/-- The literal k0 all-vertex fibre retains the chosen Fin1 product base. -/
def literalZeroEdgeTupleFibre (W : SimplicialSpace.{u})
    (x : Fin 1 → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (zeroEdgeVertexMap W) (zeroEdgePoint W x)


/-- The literal Fin1 zero-edge fibre is compared to the same normalized original fibre. -/
def literalZeroEdgeTupleFibreIso (W : SimplicialSpace.{u})
    (x : Fin 1 → (W.diagram _⦋0⦌) _⦋0⦌) :
    literalZeroEdgeTupleFibre W x ≅ zeroEdgeTupleFibre W (x 0) := by
  dsimp only [literalZeroEdgeTupleFibre]
  let e := productUniqueIso (fun _ : Fin 1 => W.diagram _⦋0⦌)
  have f_eq : zeroEdgeVertexMap W = (𝟙 (W.diagram _⦋0⦌)) ≫ e.inv :=
    (zeroEdgeVertexMap_eq W).trans (Category.id_comp _).symm
  exact pullback.congrHom f_eq (zeroEdgePoint_eq W x) ≪≫
    pullbackPostIso (𝟙 (W.diagram _⦋0⦌)) (SSet.yonedaEquiv.symm (x 0)) e.symm


set_option linter.unusedVariables false in
/-- The literal k0 fibre reaches its actual empty product via the same two terminal comparisons. -/
def literalZeroEdgeTupleFibreProductIso (W : SimplicialSpace.{u})
    (x : Fin 1 → (W.diagram _⦋0⦌) _⦋0⦌) :
    literalZeroEdgeTupleFibre W x ≅ ∏ᶜ (fun i : Fin 0 => mappingFibre W (x 0) (x 0)) :=
  literalZeroEdgeTupleFibreIso W x ≪≫ zeroEdgeTupleFibreProductIso W (x 0)


end SimplicialSpace.FixedTupleSpineBoundary
