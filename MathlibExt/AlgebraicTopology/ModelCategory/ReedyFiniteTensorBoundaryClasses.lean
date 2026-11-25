/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.PartialDegeneracyLatching
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.EpiInsertion
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.CategoryTheory.Reedy.Corner

/-!
# Original coefficient copies in the actual finite tensor PP source -/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- Every original tensor coefficient copy followed by an original transformation. -/
def copyThrough (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)]
    {P : SimplicialObject C} (f : tensor F K ⟶ P) (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    F.obj n ⟶ P.obj n := inclusion F K n k ≫ f.app n

/-- Every original simplex operator acts naturally on its original coefficient copy. -/
@[reassoc]
theorem copyThrough_naturality (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)]
    {P : SimplicialObject C} (f : tensor F K ⟶ P) {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m)
    (k : K.obj n) :
    F.map g ≫ copyThrough F K f m (K.map g k) = copyThrough F K f n k ≫ P.map g := by
  have h := congrArg (fun z => inclusion F K n k ≫ z) (f.naturality g)
  simpa only [copyThrough, Category.assoc, inclusion_tensor_map_assoc] using h

section Pushout

variable [HasPushouts C] {F F' : SimplicialObject C} (i : F ⟶ F')
  {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)

/-- Each original K copy of the target coefficient appears through the actual first pushout leg. -/
def pushoutSourceOldCopy (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    F'.obj n ⟶ (pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).obj n :=
  copyThrough F' K (pushout.inl _ _) n k

/-- Each original L copy of the source coefficient appears through the actual second pushout leg. -/
def pushoutSourceNewCopy (n : SimplexCategoryᵒᵖ) (l : L.obj n) :
    F.obj n ⟶ (pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).obj n :=
  copyThrough F L (pushout.inr _ _) n l

/-- The actual PP keeps each original old coefficient copy and its original j value. -/
@[reassoc]
theorem pushoutSourceOldCopy_map (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    pushoutSourceOldCopy i j n k ≫ (pushoutProduct i j).app n = inclusion F' L n (j.app n k) := by
  dsimp only [pushoutSourceOldCopy, copyThrough]
  rw [Category.assoc]
  exact (congrArg (fun z => inclusion F' K n k ≫ z) (congr_app (pushoutProduct_inl i j) n)).trans
    ((inclusion_tensorMap (𝟙 F') j n k).trans (Category.id_comp _))

/-- The actual PP keeps each original new coefficient copy and its original i value. -/
@[reassoc]
theorem pushoutSourceNewCopy_map (n : SimplexCategoryᵒᵖ) (l : L.obj n) :
    pushoutSourceNewCopy i j n l ≫ (pushoutProduct i j).app n = i.app n ≫ inclusion F' L n l := by
  dsimp only [pushoutSourceNewCopy, copyThrough]
  rw [Category.assoc]
  exact (congrArg (fun z => inclusion F L n l ≫ z) (congr_app (pushoutProduct_inr i j) n)).trans
    (inclusion_tensorMap i (𝟙 L) n l)

/-- The source pushout retains the original relation between each old and new coefficient copy. -/
@[reassoc]
theorem pushoutSourceCopy_relation (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    i.app n ≫ pushoutSourceOldCopy i j n k = pushoutSourceNewCopy i j n (j.app n k) := by
  have h := congr_app (pushout.condition (f := tensorMap i (𝟙 K)) (g := tensorMap (𝟙 F) j)) n
  have hc := congrArg (fun z => inclusion F K n k ≫ z) h
  simpa only [pushoutSourceOldCopy, pushoutSourceNewCopy, copyThrough, NatTrans.comp_app,
    inclusion_tensorMap_assoc, NatTrans.id_app, CategoryTheory.types_id_apply, Category.id_comp]
        using hc

/-- All original simplex operators preserve the actual old-copy source map. -/
@[reassoc]
theorem pushoutSourceOldCopy_naturality {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) (k : K.obj n) :
    F'.map g ≫ pushoutSourceOldCopy i j m (K.map g k) =
      pushoutSourceOldCopy i j n k ≫ (pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).map g :=
  copyThrough_naturality F' K (pushout.inl _ _) g k

/-- All original simplex operators preserve the actual new-copy source map. -/
@[reassoc]
theorem pushoutSourceNewCopy_naturality {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) (l : L.obj n) :
    F.map g ≫ pushoutSourceNewCopy i j m (L.map g l) =
      pushoutSourceNewCopy i j n l ≫ (pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).map g :=
  copyThrough_naturality F L (pushout.inr _ _) g l

end Pushout

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-! # The original coefficient and lower maps of a Reedy latching-corner datum -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uD uC vC

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.Shape

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
  {F G : J ⥤ C} (i : F ⟶ G) (j : J) {E : C}
  (t : pushout (latchingMap r F j) (colimMap (r.latchingTransformation i j)) ⟶ E)

/-- The original coefficient map specified by a map out of the actual corner. -/
def latchingCornerTop : F.obj j ⟶ E :=
  pushout.inl (latchingMap r F j) (colimMap (r.latchingTransformation i j)) ≫ t

/-- The original lower target map specified by a map out of the actual corner. -/
def latchingCornerLower : colimit (r.latchingDiagram G j) ⟶ E :=
  pushout.inr (latchingMap r F j) (colimMap (r.latchingTransformation i j)) ≫ t

/-- Every original latching triangle is retained by the complete actual corner datum. -/
@[reassoc]
theorem latchingCornerData_naturality (a : r.Latching j) :
    F.map (r.latchingArrow a) ≫ latchingCornerTop r i j t =
      i.app (r.latchingSource a) ≫ colimit.ι (r.latchingDiagram G j) a ≫ latchingCornerLower r i j
          t := by
  dsimp only [latchingCornerTop, latchingCornerLower]
  rw [← latchingMap_ι r F j a, Category.assoc, pushout.condition_assoc, ι_colimMap_assoc]
  rfl

/-- An original corner square gives its original coefficient square. -/
theorem latchingCornerData_coefficientSquare {B : C} (p : E ⟶ B) (b : G.obj j ⟶ B)
    (sq : CommSq t (latchingCorner r i j) p b) :
    CommSq (latchingCornerTop r i j t) (i.app j) p b := by
  constructor
  dsimp only [latchingCornerTop]
  rw [Category.assoc, sq.w, latchingCorner_inl_assoc]

/-- An original corner square gives its original whole lower-target equation. -/
@[reassoc]
theorem latchingCornerData_lowerSquare {B : C} (p : E ⟶ B) (b : G.obj j ⟶ B)
    (sq : CommSq t (latchingCorner r i j) p b) :
    latchingCornerLower r i j t ≫ p = latchingMap r G j ≫ b := by
  dsimp only [latchingCornerLower]
  rw [Category.assoc, sq.w, latchingCorner_inr_assoc]

end CategoryTheory.ReedyStructure.Shape

end
end
end

section



/-!
# The original tensor copies of partial epi-factor latching diagrams

Every partial-factor object labels its tensor coefficient by its original
unique residual simplex map. All original comparison and incoming epi maps
are retained, and give complete naturality on the actual tensor diagram.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

/-- The actual standard-simplex label of each original residual epi factor. -/
def factorLabel {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : SimplexCategory.PartialLatching.Index α) :
    (Δ[d] : SSet.{v}).obj (SimplexCategory.PartialLatching.source a) :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialLatching.factor α a)

/-- Every original partial comparison acts on the same original residual simplex. -/
theorem factorLabel_comparison {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    {a b : SimplexCategory.PartialLatching.Index α} (f : a ⟶ b) :
    (Δ[d] : SSet.{v}).map (SimplexCategory.PartialLatching.comparison f) (factorLabel α a) =
      factorLabel α b := by
  change SSet.stdSimplex.objEquiv.symm
      ((SimplexCategory.PartialLatching.comparison f).unop ≫ SimplexCategory.PartialLatching.factor
          α a) = _
  exact congrArg SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.PartialLatching.factor_naturality α f).symm

/-- Every original incoming epi sends its residual simplex to the unchanged original simplex. -/
theorem factorLabel_arrow {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : SimplexCategory.PartialLatching.Index α) :
    (Δ[d] : SSet.{v}).map (SimplexCategory.PartialLatching.arrow a) (factorLabel α a) =
      SSet.stdSimplex.objEquiv.symm α := by
  change SSet.stdSimplex.objEquiv.symm
      ((SimplexCategory.PartialLatching.arrow a).unop ≫ SimplexCategory.PartialLatching.factor α a)
          = _
  exact congrArg SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialLatching.factor_eq α a)

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- The literal original coefficient diagram restricted to every retained original epi factor. -/
abbrev partialSourceRestriction (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    SimplexCategory.PartialLatching.Index α ⥤ C :=
  SimplexCategory.PartialLatching.inclusion α ⋙ SimplexCategory.reedyOp.latchingDiagram F (op ⦋m⦌)

/-- All original partial coefficients embed in the actual tensor diagram at their original residual
labels. -/
def factorCopyTransformation (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    partialSourceRestriction F α ⟶ partialSourceRestriction (tensor F (Δ[d] : SSet.{v})) α where
  app a := inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a)
      (factorLabel α a)
  naturality {a b} f := by
    change F.map (SimplexCategory.PartialLatching.comparison f) ≫
        inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source b) (factorLabel α b) =
      inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a) ≫
        (tensor F (Δ[d] : SSet.{v})).map (SimplexCategory.PartialLatching.comparison f)
    rw [inclusion_tensor_map, factorLabel_comparison]

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-! # Original standard-boundary labels under the original epi operators -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

/-- The original residual simplex outside its original boundary is an original epimorphism. -/
theorem simplex_epi_of_not_boundary (d : ℕ) (n : SimplexCategoryᵒᵖ)
    (s : (Δ[d] : SSet.{v}).obj n) (hs : s ∉ (SSet.boundary.{v} d).obj n) :
    Epi (SSet.stdSimplex.objEquiv s) := by
  apply (SimplexCategory.epi_iff_surjective (f := SSet.stdSimplex.objEquiv s)).2
  change ¬¬Function.Surjective (SSet.stdSimplex.asOrderHom s) at hs
  exact not_not.mp hs

/-- The original standard-boundary predicate is preserved and reflected by each original epi simplex
operator. -/
theorem simplex_boundary_epi_map_iff (d : ℕ) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    [Epi f.unop] (s : (Δ[d] : SSet.{v}).obj n) :
    (Δ[d] : SSet.{v}).map f s ∈ (SSet.boundary.{v} d).obj m ↔ s ∈ (SSet.boundary.{v} d).obj n := by
  have hg : Function.Surjective f.unop.toOrderHom :=
      (SimplexCategory.epi_iff_surjective (f := f.unop)).1 inferInstance
  change (¬Function.Surjective ((SSet.stdSimplex.objEquiv s).toOrderHom ∘ f.unop.toOrderHom)) ↔
    ¬Function.Surjective (SSet.stdSimplex.objEquiv s).toOrderHom
  constructor
  · intro h hs
    exact h (hs.comp hg)
  · intro h hs
    exact h (Function.Surjective.of_comp hs)

/-- The original residual partial factor is outside the original boundary whenever its original
target simplex is. -/
theorem factorLabel_not_boundary {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (ha : SSet.stdSimplex.objEquiv.symm α ∉ (SSet.boundary.{v} d).obj (op ⦋m⦌))
    (a : SimplexCategory.PartialLatching.Index α) :
    factorLabel.{v} α a ∉ (SSet.boundary.{v} d).obj (SimplexCategory.PartialLatching.source a) := by
  rw [← simplex_boundary_epi_map_iff d (SimplexCategory.PartialLatching.arrow a), factorLabel_arrow]
  exact ha

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Original finite tensor geometry at the zero simplex boundary

The actual tensor with Δ[0] retains the complete original coefficient diagram.
The actual tensor with ∂Δ[0] is initial. These geometric facts compare the
original tensor boundary pushout and every original Reedy latching corner.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C]

section Tensor

variable [HasFiniteCoproducts C]

/-- Each original zero-simplex degree has its one actual constant simplex. -/
instance stdZeroUnique (n : SimplexCategoryᵒᵖ) : Unique ((Δ[0] : SSet.{v}).obj n) where
  default := SSet.stdSimplex.objEquiv.symm (SimplexCategory.const n.unop ⦋0⦌ 0)
  uniq _ := SSet.stdSimplex.objEquiv.injective (Subsingleton.elim _ _)

/-- Every original zero-boundary degree is empty. -/
instance boundaryZeroIsEmpty (n : SimplexCategoryᵒᵖ) :
    IsEmpty ((∂Δ[0] : SSet.{v}).obj n) :=
  ⟨fun ⟨_, hk⟩ => by simp at hk⟩

/-- The singleton tensor collapse keeps the identity on every original coefficient copy. -/
def tensorSingletonHom (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Unique (K.obj n)] :
    tensor F K ⟶ F where
  app n := Sigma.desc (fun _ => 𝟙 (F.obj n))
  naturality {n m} f := by
    apply Sigma.hom_ext
    intro k
    change Sigma.ι (fun _ : K.obj n => F.obj n) k ≫
        Sigma.map' (K.map f) (fun _ => F.map f) ≫ Sigma.desc (fun _ => 𝟙 (F.obj m)) =
      Sigma.ι (fun _ : K.obj n => F.obj n) k ≫ Sigma.desc (fun _ => 𝟙 (F.obj n)) ≫ F.map f
    rw [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    rw [Category.comp_id, Category.id_comp]

/-- The singleton tensor inclusion keeps the original unique simplex at every degree. -/
def tensorSingletonInv (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Unique (K.obj n)] :
    F ⟶ tensor F K where
  app n := inclusion F K n default
  naturality {n m} f := by
    rw [inclusion_tensor_map]
    exact congrArg (fun k : K.obj m => F.map f ≫ inclusion F K m k) (Subsingleton.elim _ _)

/-- The actual singleton tensor is the complete original coefficient diagram. -/
def tensorSingletonIso (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Unique (K.obj n)] :
    tensor F K ≅ F where
  hom := tensorSingletonHom F K
  inv := tensorSingletonInv F K
  hom_inv_id := by
    ext n
    apply Sigma.hom_ext
    intro k
    change Sigma.ι (fun _ : K.obj n => F.obj n) k ≫ Sigma.desc (fun _ => 𝟙 (F.obj n)) ≫
        Sigma.ι (fun _ : K.obj n => F.obj n) default =
      Sigma.ι (fun _ : K.obj n => F.obj n) k ≫ 𝟙 _
    rw [Sigma.ι_comp_desc_assoc, Category.id_comp, Category.comp_id]
    exact congrArg (fun k : K.obj n => Sigma.ι (fun _ : K.obj n => F.obj n) k)
      (Subsingleton.elim _ _)
  inv_hom_id := by
    ext n
    change Sigma.ι (fun _ : K.obj n => F.obj n) default ≫ Sigma.desc (fun _ => 𝟙 (F.obj n)) = 𝟙 _
    exact Sigma.ι_comp_desc (fun _ => 𝟙 (F.obj n)) default

/-- Every original coefficient map is retained by the entire singleton tensor collapse. -/
@[reassoc]
theorem tensorSingletonIso_naturality {F F' : SimplicialObject C} (i : F ⟶ F')
    (K : SSet.{v}) [∀ n, Unique (K.obj n)] :
    tensorMap i (𝟙 K) ≫ (tensorSingletonIso F' K).hom = (tensorSingletonIso F K).hom ≫ i := by
  ext n
  apply Sigma.hom_ext
  intro k
  change Sigma.ι (fun _ : K.obj n => F.obj n) k ≫
      Sigma.map' (fun k : K.obj n => k) (fun _ => i.app n) ≫ Sigma.desc (fun _ => 𝟙 (F'.obj n)) =
    Sigma.ι (fun _ : K.obj n => F.obj n) k ≫ Sigma.desc (fun _ => 𝟙 (F.obj n)) ≫ i.app n
  rw [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  rw [Category.comp_id, Category.id_comp]

/-- The tensor of an actual empty simplicial set is an initial original diagram. -/
def tensorEmptyIsInitial (F : SimplicialObject C) (K : SSet.{v}) [∀ n, IsEmpty (K.obj n)] :
    IsInitial (tensor F K) :=
  IsInitial.ofUniqueHom
    (fun G =>
      { app n := Sigma.desc (fun k => isEmptyElim k)
        naturality {n m} f := by
          apply Sigma.hom_ext
          intro k
          exact isEmptyElim k })
    (fun G f => by
      ext n
      apply Sigma.hom_ext
      intro k
      exact isEmptyElim k)

/-- The whole actual tensor by Δ[0], with all original simplex actions, is the original diagram. -/
def tensorStdZeroIso (F : SimplicialObject C) : tensor F (Δ[0] : SSet.{v}) ≅ F :=
  tensorSingletonIso F _

/-- Tensor by the original zero boundary is an actual initial simplicial diagram. -/
def tensorBoundaryZeroIsInitial (F : SimplicialObject C) :
    IsInitial (tensor F (∂Δ[0] : SSet.{v})) :=
  tensorEmptyIsInitial F _

/-- Each original zero-simplex inclusion collapses to the original coefficient identity. -/
@[reassoc]
theorem tensorStdZeroIso_inclusion (F : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (k : (Δ[0] : SSet.{v}).obj n) :
    inclusion F (Δ[0] : SSet.{v}) n k ≫ (tensorStdZeroIso F).hom.app n = 𝟙 (F.obj n) := by
  change Sigma.ι (fun _ : (Δ[0] : SSet.{v}).obj n => F.obj n) k ≫
    Sigma.desc (fun _ => 𝟙 (F.obj n)) = 𝟙 _
  exact Sigma.ι_comp_desc _ _

/-- Every original coefficient arrow is the same entire singleton tensor arrow. -/
def tensorStdZeroArrowIso {F F' : SimplicialObject C} (i : F ⟶ F') :
    Arrow.mk (tensorMap i (𝟙 (Δ[0] : SSet.{v}))) ≅ Arrow.mk i :=
  Arrow.isoMk (tensorStdZeroIso F) (tensorStdZeroIso F')
    (tensorSingletonIso_naturality i (Δ[0] : SSet.{v})).symm

/-- The original coefficient map on the actual empty boundary tensor is an isomorphism. -/
theorem tensorBoundaryZeroMap_isIso {F F' : SimplicialObject C} (i : F ⟶ F') :
    IsIso (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) :=
  isIso_of_isInitial (tensorBoundaryZeroIsInitial F) (tensorBoundaryZeroIsInitial F') _

end Tensor

section Reedy

variable [HasFiniteColimits C]

/-- Every actual zero-simplex tensor latching corner is the original coefficient latching corner. -/
def tensorStdZeroLatchingCornerIso {F F' : SimplicialObject C} (i : F ⟶ F')
    (n : SimplexCategoryᵒᵖ) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (tensorMap i (𝟙 (Δ[0] : SSet.{v}))) n) ≅
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n) :=
  (CategoryTheory.ReedyStructure.latchingCornerArrow SimplexCategory.reedyOp n).mapIso
      (tensorStdZeroArrowIso i)

/-- The original tensor square for the original zero-boundary inclusion commutes. -/
theorem boundaryZeroSquare {F F' : SimplicialObject C} (i : F ⟶ F') :
    tensorMap i (𝟙 (∂Δ[0] : SSet.{v})) ≫ tensorMap (𝟙 F') (SSet.boundary.{v} 0).ι =
      tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι ≫ tensorMap i (𝟙 (Δ[0] : SSet.{v})) := by
  rw [← tensorMap_comp, ← tensorMap_comp]
  simp

/-- The actual tensor pushout-product map for the original zero-boundary inclusion. -/
def boundaryZeroPushoutProduct {F F' : SimplicialObject C} (i : F ⟶ F') :
    pushout (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι) ⟶
      tensor F' (Δ[0] : SSet.{v}) :=
  pushout.desc (tensorMap (𝟙 F') (SSet.boundary.{v} 0).ι)
    (tensorMap i (𝟙 (Δ[0] : SSet.{v}))) (boundaryZeroSquare i)

/-- The first original pushout injection recovers the original scalar boundary tensor map. -/
@[reassoc]
theorem boundaryZeroPushoutProduct_inl {F F' : SimplicialObject C} (i : F ⟶ F') :
    pushout.inl (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι) ≫
        boundaryZeroPushoutProduct i = tensorMap (𝟙 F') (SSet.boundary.{v} 0).ι :=
  pushout.inl_desc _ _ _

/-- The second original pushout injection recovers the entire original coefficient tensor map. -/
@[reassoc]
theorem boundaryZeroPushoutProduct_inr {F F' : SimplicialObject C} (i : F ⟶ F') :
    pushout.inr (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι) ≫
        boundaryZeroPushoutProduct i = tensorMap i (𝟙 (Δ[0] : SSet.{v})) :=
  pushout.inr_desc _ _ _

/-- The actual zero-boundary tensor pushout has the original coefficient source. -/
def boundaryZeroSourceIso {F F' : SimplicialObject C} (i : F ⟶ F') :
    pushout (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι) ≅ F := by
  letI := tensorBoundaryZeroMap_isIso i
  exact (asIso (pushout.inr (tensorMap i (𝟙 (∂Δ[0] : SSet.{v})))
    (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι))).symm ≪≫ tensorStdZeroIso F

/-- The original nonempty pushout injection is exactly the original singleton tensor collapse. -/
@[reassoc]
theorem boundaryZeroSourceIso_inr_hom {F F' : SimplicialObject C} (i : F ⟶ F') :
    pushout.inr (tensorMap i (𝟙 (∂Δ[0] : SSet.{v}))) (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι) ≫
        (boundaryZeroSourceIso i).hom = (tensorStdZeroIso F).hom := by
  let _ := tensorBoundaryZeroMap_isIso i
  change pushout.inr _ _ ≫ (inv (pushout.inr _ _) ≫ (tensorStdZeroIso F).hom) = _
  exact IsIso.hom_inv_id_assoc _ _

/-- The complete original zero-boundary tensor pushout-product arrow is the original coefficient
arrow. -/
def boundaryZeroPushoutProductArrowIso {F F' : SimplicialObject C} (i : F ⟶ F') :
    Arrow.mk (boundaryZeroPushoutProduct i) ≅ Arrow.mk i := by
  letI := tensorBoundaryZeroMap_isIso i
  refine Arrow.isoMk (boundaryZeroSourceIso i) (tensorStdZeroIso F') ?_
  change (boundaryZeroSourceIso i).hom ≫ i = boundaryZeroPushoutProduct i ≫
      (tensorStdZeroIso F').hom
  apply (cancel_epi (pushout.inr (tensorMap i (𝟙 (∂Δ[0] : SSet.{v})))
    (tensorMap (𝟙 F) (SSet.boundary.{v} 0).ι))).1
  rw [← Category.assoc, boundaryZeroSourceIso_inr_hom, ← Category.assoc,
      boundaryZeroPushoutProduct_inr]
  exact (tensorSingletonIso_naturality i (Δ[0] : SSet.{v})).symm

/-- Every actual zero-boundary pushout-product latching corner is the original coefficient latching
corner. -/
def boundaryZeroPushoutProductLatchingCornerIso {F F' : SimplicialObject C} (i : F ⟶ F')
    (n : SimplexCategoryᵒᵖ) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
        (boundaryZeroPushoutProduct i) n) ≅
      Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n) :=
  (CategoryTheory.ReedyStructure.latchingCornerArrow SimplexCategory.reedyOp n).mapIso
    (boundaryZeroPushoutProductArrowIso i)

end Reedy

section Model

variable [ModelCategory C]

/-- The actual singleton tensor retains the Reedy cofibration class at every original degree. -/
theorem tensorStdZero_reedyCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (tensorMap i (𝟙 (Δ[0] : SSet.{v}))) n) :=
  ((cofibrations C).arrow_mk_iso_iff (tensorStdZeroLatchingCornerIso i n)).2 (hi n)

/-- The actual singleton tensor retains the Reedy trivial cofibration class at every original
degree. -/
theorem tensorStdZero_reedyTrivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (tensorMap i (𝟙 (Δ[0] : SSet.{v}))) n) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (tensorStdZeroLatchingCornerIso i n)).2 (hi n)

/-- The original zero-boundary pushout product is a Reedy cofibration from the original source Reedy
cofibration. -/
theorem boundaryZeroPushoutProduct_reedyCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (boundaryZeroPushoutProduct i) n) :=
  ((cofibrations C).arrow_mk_iso_iff (boundaryZeroPushoutProductLatchingCornerIso i n)).2 (hi n)

/-- The original zero-boundary pushout product is a Reedy trivial cofibration from the original
source Reedy
trivial cofibration. -/
theorem boundaryZeroPushoutProduct_reedyTrivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C
      (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
          (boundaryZeroPushoutProduct i) n) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (boundaryZeroPushoutProductLatchingCornerIso i n)).2
      (hi n)

end Model

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Original native finite-pair boundary-zero Reedy corners

The whole native tensor pushout-product factory at the original zero boundary
is exactly the proved boundary-zero recipe. Its complete original Arrow and
all actual latching corners are compared with the original coefficient arrow.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C]

section Geometry

variable [HasFiniteColimits C]

/-- The complete original boundary-zero recipe is the complete original native tensor PP factory. -/
theorem boundaryZeroFactory_eq_native :
    (fun {F F' : SimplicialObject C} (i : F ⟶ F') => boundaryZeroPushoutProduct i) =
      (fun {F F' : SimplicialObject C} (i : F ⟶ F') => pushoutProduct i (SSet.boundary.{v} 0).ι) :=
  rfl

/-- The unchanged whole native boundary-zero tensor PP arrow is the original coefficient arrow. -/
def nativeBoundaryZeroArrowIso {F F' : SimplicialObject C} (i : F ⟶ F') :
    Arrow.mk (pushoutProduct i (SSet.boundary.{v} 0).ι) ≅ Arrow.mk i := by
  rw [← congrFun (congrFun (congrFun boundaryZeroFactory_eq_native F) F') i]
  exact boundaryZeroPushoutProductArrowIso i

/-- All original native boundary-zero latching corners retain the full original coefficient corners.
-/
def nativeBoundaryZeroLatchingCornerIso {F F' : SimplicialObject C} (i : F ⟶ F')
    (n : SimplexCategoryᵒᵖ) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} 0).ι) n) ≅
      Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n) :=
  (CategoryTheory.ReedyStructure.latchingCornerArrow SimplexCategory.reedyOp n).mapIso
      (nativeBoundaryZeroArrowIso i)

end Geometry

section Model

variable [ModelCategory C]

/-- The actual native zero-boundary tensor PP has every Reedy cofibration corner of its original
coefficient source. -/
theorem nativeBoundaryZero_reedyCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} 0).ι) n) :=
  ((cofibrations C).arrow_mk_iso_iff (nativeBoundaryZeroLatchingCornerIso i n)).2 (hi n)

/-- The actual native zero-boundary tensor PP has every Reedy trivial cofibration corner of its
original
coefficient source. -/
theorem nativeBoundaryZero_reedyTrivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ n, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} 0).ι) n) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (nativeBoundaryZeroLatchingCornerIso i n)).2 (hi n)

/-- Original Reedy cofibration and original objectwise weak data give the native boundary-zero
trivial corner. -/
theorem nativeBoundaryZero_reedyTrivialCofibration_of_cofibration_weak
    {F F' : SimplicialObject C} (i : F ⟶ F')
    (hc : ∀ n, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i n))
    (hw : ∀ n, weakEquivalences C (i.app n)) (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} 0).ι) n) :=
  nativeBoundaryZero_reedyTrivialCofibration i
    (ReedyModel.latchingCorner_trivialCofibration_of_cofibration_weak
      SimplexCategory.reedyOp i hc hw) n

end Model

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Native tensor boundaries below their first new simplex

The original boundary inclusion is a bijection in every degree below its
standard simplex. The original finite tensor PP and its complete actual
latching corner are therefore isomorphisms in those degrees. No coefficient
cofibration or model preservation outcome is needed for this geometry.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C]

section Scalar

variable [HasFiniteCoproducts C]

/-- An actual scalar degree bijection gives the original tensor degree isomorphism. -/
theorem tensorScalarApp_isIso_of_bijective (F : SimplicialObject C)
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (hj : Function.Bijective (j.app n)) :
    IsIso ((tensorMap (𝟙 F) j).app n) := by
  let e := Equiv.ofBijective (j.app n) hj
  have h : (tensorMap (𝟙 F) j).app n = (Sigma.reindex e (fun _ : L.obj n => F.obj n)).hom := by
    change Sigma.map' (f := fun _ : L.obj n => F.obj n) (g := fun _ : K.obj n => F.obj n)
      (j.app n) (fun _ => 𝟙 (F.obj n)) = _
    apply Sigma.hom_ext
    intro k
    rw [Sigma.ι_comp_map', Category.id_comp]
    exact (Sigma.ι_reindex_hom e (fun _ : L.obj n => F.obj n) k).symm
  rw [h]
  exact (Sigma.reindex e (fun _ : L.obj n => F.obj n)).isIso_hom

/-- Every original scalar boundary inclusion is bijective strictly below its own degree. -/
theorem boundary_inclusion_bijective_before (d : ℕ) (n : SimplexCategoryᵒᵖ)
    (hn : n.unop.len < d) : Function.Bijective ((SSet.boundary.{v} d).ι.app n) := by
  constructor
  · exact Subtype.val_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [SSet.boundary_obj_eq_univ n.unop.len d hn]
    exact Set.mem_univ x

end Scalar

section Geometry

variable [HasFiniteColimits C]

/-- The actual native finite tensor pushout-product square remains a pushout in every original
degree. -/
theorem nativePushoutProductDegreeIsPushout {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) :
    IsPushout ((tensorMap i (𝟙 K)).app n) ((tensorMap (𝟙 F) j).app n)
      ((pushout.inl (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).app n)
      ((pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)).app n) :=
  ((evaluation SimplexCategoryᵒᵖ C).obj n).map_isPushout
    (IsPushout.of_hasPushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j))

/-- The actual native PP degree is an isomorphism whenever the original scalar degree map is
bijective. -/
theorem nativePushoutProductApp_isIso_of_bijective {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (hj : Function.Bijective (j.app n)) :
    IsIso ((pushoutProduct i j).app n) := by
  let _ := tensorScalarApp_isIso_of_bijective F j n hj
  let _ := (nativePushoutProductDegreeIsPushout i j n).isIso_inl_of_isIso
  let _ := tensorScalarApp_isIso_of_bijective F' j n hj
  exact IsIso.of_isIso_fac_left (congr_app (pushoutProduct_inl i j) n)

/-- The original native boundary tensor PP has no new coefficient map below the standard simplex
degree. -/
theorem nativeBoundaryPushoutProductApp_isIso_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    IsIso ((pushoutProduct i (SSet.boundary.{v} d).ι).app n) :=
  nativePushoutProductApp_isIso_of_bijective i _ n (boundary_inclusion_bijective_before d n hn)

/-- The whole original lower latching transformation is an isomorphism below the standard simplex
degree. -/
theorem nativeBoundaryLatchingTransformation_isIso_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    IsIso (SimplexCategory.reedyOp.latchingTransformation
        (pushoutProduct i (SSet.boundary.{v} d).ι) n) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro a
  change IsIso
      ((pushoutProduct i (SSet.boundary.{v} d).ι).app (SimplexCategory.reedyOp.latchingSource a))
  exact nativeBoundaryPushoutProductApp_isIso_before i d _ (a.property.trans hn)

/-- The actual original latching colimit comparison is an isomorphism below the standard simplex
degree. -/
theorem nativeBoundaryLatchingComparison_isIso_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    IsIso (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) n)) := by
  let _ := nativeBoundaryLatchingTransformation_isIso_before i d n hn
  infer_instance

/-- The complete native Reedy latching corner is an isomorphism below the standard simplex degree.
-/
theorem nativeBoundaryLatchingCorner_isIso_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    IsIso (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) := by
  let _ := nativeBoundaryLatchingComparison_isIso_before i d n hn
  let _ := nativeBoundaryPushoutProductApp_isIso_before i d n hn
  have h := CategoryTheory.ReedyStructure.latchingCorner_inl SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) n
  exact IsIso.of_isIso_fac_left h

end Geometry

section Model

variable [ModelCategory C]

/-- Every actual native boundary PP corner before its scalar simplex is a source cofibration. -/
theorem nativeBoundary_reedyCofibration_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) := by
  let _ := nativeBoundaryLatchingCorner_isIso_before i d n hn
  exact (cofibrations C).of_isIso _

/-- Every actual native boundary PP corner before its scalar simplex is a source trivial
cofibration. -/
theorem nativeBoundary_reedyTrivialCofibration_before {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len < d) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) := by
  let _ := nativeBoundaryLatchingCorner_isIso_before i d n hn
  exact (trivialCofibrations C).of_isIso _

end Model

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Actual finite tensor PP component and first-boundary corner classes

The full original evaluated tensor pushout square is compared with its
original finite scalar copower square. Scalar model laws derive every
component cofibration and trivial cofibration. For a standard boundary,
the actual Reedy corner through its first new simplex is the same original
component arrow; higher relative degeneracy corners remain separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C]

section Pushout

variable {W X Y P Z : C} {f : W ⟶ X} {g : W ⟶ Y}
  {inl : X ⟶ P} {inr : Y ⟶ P} [HasPushout f g]

/-- A complete original pushout and its original target cocone give the same complete Arrow. -/
def pushoutDescArrowIso (hp : IsPushout f g inl inr) (a : X ⟶ Z) (b : Y ⟶ Z)
    (h : f ≫ a = g ≫ b) (q : P ⟶ Z) (hl : inl ≫ q = a) (hr : inr ≫ q = b) :
    Arrow.mk q ≅ Arrow.mk (pushout.desc a b h) := by
  refine Arrow.isoMk hp.isoPushout (Iso.refl _) ?_
  change hp.isoPushout.hom ≫ pushout.desc a b h = q ≫ 𝟙 Z
  rw [Category.comp_id]
  apply hp.hom_ext
  · rw [← Category.assoc, hp.inl_isoPushout_hom, pushout.inl_desc]
    exact hl.symm
  · rw [← Category.assoc, hp.inr_isoPushout_hom, pushout.inr_desc]
    exact hr.symm

end Pushout

section Geometry

variable [HasFiniteColimits C]

/-- The original native tensor PP degree arrow is the original finite scalar copower PP arrow. -/
def nativePushoutProductAppArrowIso {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) :
    Arrow.mk ((pushoutProduct i j).app n) ≅
      Arrow.mk (FiniteCopowerPushout.map (i.app n) (j.app n)) := by
  exact pushoutDescArrowIso (nativePushoutProductDegreeIsPushout i j n)
    ((tensorMap (𝟙 F') j).app n) ((tensorMap i (𝟙 L)).app n)
    (congr_app (tensorMap_square i j) n) ((pushoutProduct i j).app n)
    (congr_app (pushoutProduct_inl i j) n) (congr_app (pushoutProduct_inr i j) n)

/-- At and below the first scalar boundary degree, the complete original lower latching
transformation is an
isomorphism. -/
theorem nativeBoundaryLatchingTransformation_isIso_le {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len ≤ d) :
    IsIso (SimplexCategory.reedyOp.latchingTransformation
        (pushoutProduct i (SSet.boundary.{v} d).ι) n) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro a
  change IsIso
      ((pushoutProduct i (SSet.boundary.{v} d).ι).app (SimplexCategory.reedyOp.latchingSource a))
  exact nativeBoundaryPushoutProductApp_isIso_before i d _ (a.property.trans_le hn)

/-- At and below the first scalar boundary degree, the complete original latching comparison is an
isomorphism. -/
theorem nativeBoundaryLatchingComparison_isIso_le {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len ≤ d) :
    IsIso (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) n)) := by
  let _ := nativeBoundaryLatchingTransformation_isIso_le i d n hn
  infer_instance

/-- The complete actual latching corner through the first boundary simplex is the original native
component arrow. -/
def nativeBoundaryLatchingCornerComponentIsoLe {F F' : SimplicialObject C} (i : F ⟶ F')
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len ≤ d) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) ≅
      Arrow.mk ((pushoutProduct i (SSet.boundary.{v} d).ι).app n) := by
  letI := nativeBoundaryLatchingComparison_isIso_le i d n hn
  let inl := pushout.inl
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      (pushout (tensorMap i (𝟙 (SSet.boundary.{v} d : SSet.{v})))
        (tensorMap (𝟙 F) (SSet.boundary.{v} d).ι)) n)
    (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) n))
  letI : IsIso inl := by dsimp only [inl]; infer_instance
  refine Arrow.isoMk (asIso inl).symm (Iso.refl _) ?_
  change inv inl ≫ (pushoutProduct i (SSet.boundary.{v} d).ι).app n =
    CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n ≫ 𝟙 _
  apply (cancel_epi inl).1
  rw [IsIso.hom_inv_id_assoc, Category.comp_id]
  exact (CategoryTheory.ReedyStructure.latchingCorner_inl SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) n).symm

end Geometry

section Model

variable [ModelCategory C]

/-- Source scalar cofibration and actual scalar injectivity give the original native tensor PP
component cofibration. -/
theorem nativePushoutProductApp_cofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (hi : cofibrations C (i.app n)) (hj : Function.Injective (j.app n)) :
    cofibrations C ((pushoutProduct i j).app n) :=
  ((cofibrations C).arrow_mk_iso_iff (nativePushoutProductAppArrowIso i j n)).2
    (FiniteCopowerPushout.cofibration (i.app n) (j.app n) hi hj)

/-- Source scalar trivial cofibration and actual scalar injectivity give the original native tensor
PP
component trivial cofibration. -/
theorem nativePushoutProductApp_trivialCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (hi : trivialCofibrations C (i.app n))
        (hj : Function.Injective (j.app n)) :
    trivialCofibrations C ((pushoutProduct i j).app n) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (nativePushoutProductAppArrowIso i j n)).2
    (FiniteCopowerPushout.trivialCofibration (i.app n) (j.app n) hi hj)

/-- Actual source Reedy cofibration corners derive every native finite tensor PP component
cofibration. -/
theorem nativePushoutProductApp_cofibration_of_reedy {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (hi : ∀ m, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (n : SimplexCategoryᵒᵖ) (hj : Function.Injective (j.app n)) :
    cofibrations C ((pushoutProduct i j).app n) :=
  nativePushoutProductApp_cofibration i j n
    (ReedyModel.component_cofibration_of_latchingCorners SimplexCategory.reedyOp i hi n) hj

/-- Actual source Reedy trivial corners derive every native finite tensor PP component trivial
cofibration. -/
theorem nativePushoutProductApp_trivialCofibration_of_reedy {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (hi : ∀ m, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (n : SimplexCategoryᵒᵖ) (hj : Function.Injective (j.app n)) :
    trivialCofibrations C ((pushoutProduct i j).app n) :=
  nativePushoutProductApp_trivialCofibration i j n
    (ReedyModel.component_trivialCofibration_of_latchingCorners SimplexCategory.reedyOp i hi n) hj

/-- The original standard boundary tensor PP has source cofibration corners through the first new
simplex. -/
theorem nativeBoundary_reedyCofibration_le {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ m, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len ≤ d) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) :=
  ((cofibrations C).arrow_mk_iso_iff (nativeBoundaryLatchingCornerComponentIsoLe i d n hn)).2
    (nativePushoutProductApp_cofibration_of_reedy i (SSet.boundary.{v} d).ι hi n
        Subtype.val_injective)

/-- The original standard boundary tensor PP has source trivial cofibration corners through the
first new simplex. -/
theorem nativeBoundary_reedyTrivialCofibration_le {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ m, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (d : ℕ) (n : SimplexCategoryᵒᵖ) (hn : n.unop.len ≤ d) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) n) :=
  ((trivialCofibrations C).arrow_mk_iso_iff (nativeBoundaryLatchingCornerComponentIsoLe i d n hn)).2
    (nativePushoutProductApp_trivialCofibration_of_reedy i (SSet.boundary.{v} d).ι hi n
        Subtype.val_injective)

/-- Every actual finite-degree scalar monomorphism gives all native PP component cofibrations from
source
Reedy cofibration data. -/
theorem nativePushoutProductApp_cofibration_of_reedy_mono {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L) [Mono j]
    (hi : ∀ m, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (n : SimplexCategoryᵒᵖ) : cofibrations C ((pushoutProduct i j).app n) :=
  nativePushoutProductApp_cofibration_of_reedy i j hi n (CategoryTheory.injective_of_mono (j.app n))

/-- Every actual finite-degree scalar monomorphism gives all native PP component trivial
cofibrations from
source Reedy trivial data. -/
theorem nativePushoutProductApp_trivialCofibration_of_reedy_mono {F F' : SimplicialObject C}
    (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L) [Mono j]
    (hi : ∀ m, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (n : SimplexCategoryᵒᵖ) : trivialCofibrations C ((pushoutProduct i j).app n) :=
  nativePushoutProductApp_trivialCofibration_of_reedy i j hi n
      (CategoryTheory.injective_of_mono (j.app n))

/-- Original Reedy cofibration and objectwise weak source data derive every native PP component
trivial cofibration. -/
theorem nativePushoutProductApp_trivialCofibration_of_reedy_cofibration_weak
    {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L) [Mono j]
    (hc : ∀ m, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i m))
    (hw : ∀ m, weakEquivalences C (i.app m)) (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C ((pushoutProduct i j).app n) :=
  nativePushoutProductApp_trivialCofibration_of_reedy_mono i j
    (ReedyModel.latchingCorner_trivialCofibration_of_cofibration_weak
      SimplexCategory.reedyOp i hc hw) n

end Model

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Finite original coefficient families assemble the actual native corner lift

The inputs are the original coefficient-family maps and their original
source/lower triangle equations. Finite coproduct and pushout universal
properties assemble the complete actual LiftStruct, with no model or
pushout-product preservation outcome as an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  {F F' : SimplicialObject C} (i : F ⟶ F')
  {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
  (n : SimplexCategoryᵒᵖ) {E : C}
  (t : pushout
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      (pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j)) n)
    (colimMap (SimplexCategory.reedyOp.latchingTransformation (pushoutProduct i j) n)) ⟶ E)
  (l : L.obj n → (F'.obj n ⟶ E))

/-- Actual tensor maps are determined by every original coefficient-copy restriction. -/
theorem tensorCoefficient_hom_ext (A : SimplicialObject C) (M : SSet.{v}) [∀ k, Finite (M.obj k)]
    (k : SimplexCategoryᵒᵖ) {Z : C} {f g : (tensor A M).obj k ⟶ Z}
    (h : ∀ x : M.obj k, inclusion A M k x ≫ f = inclusion A M k x ≫ g) : f = g := by
  apply Sigma.hom_ext
  intro x
  exact h x

/-- The finite family descends with the exact original native tensor endpoint. -/
def cornerFamilyDesc : (tensor F' L).obj n ⟶ E := Sigma.desc l

/-- Every original coefficient copy reads back its original finite family member. -/
@[reassoc]
theorem cornerFamilyDesc_ι (s : L.obj n) :
    inclusion F' L n s ≫ cornerFamilyDesc (F' := F') (L := L) n l = l s := by
  change Sigma.ι (fun _ : L.obj n => F'.obj n) s ≫ Sigma.desc l = l s
  exact Sigma.ι_comp_desc _ _

/-- The actual native PP component followed by the finite family is the original coefficient datum.
-/
theorem cornerFamilyDesc_component
    (hc : ∀ s : L.obj n, i.app n ≫ l s = pushoutSourceNewCopy i j n s ≫
      CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i j) n t)
    (ho : ∀ k : K.obj n, l (j.app n k) = pushoutSourceOldCopy i j n k ≫
      CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i j) n t) :
    (pushoutProduct i j).app n ≫ cornerFamilyDesc (F' := F') (L := L) n l =
      CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i j) n t := by
  apply (nativePushoutProductDegreeIsPushout i j n).hom_ext
  · apply tensorCoefficient_hom_ext F' K n
    intro k
    have h := congrArg (fun f => f ≫ cornerFamilyDesc (F' := F') (L := L) n l)
      (pushoutSourceOldCopy_map i j n k)
    have h' := (h.trans (cornerFamilyDesc_ι n l (j.app n k))).trans (ho k)
    simpa only [pushoutSourceOldCopy, copyThrough, Category.assoc] using h'
  · apply tensorCoefficient_hom_ext F L n
    intro s
    have h := congrArg (fun f => f ≫ cornerFamilyDesc (F' := F') (L := L) n l)
      (pushoutSourceNewCopy_map i j n s)
    have h' := h.trans ((Category.assoc _ _ _).trans
      (congrArg (fun f => i.app n ≫ f) (cornerFamilyDesc_ι n l s)))
    simpa only [pushoutSourceNewCopy, copyThrough, Category.assoc] using h'.trans (hc s)

/-- The complete original latching target followed by the family is the original lower datum. -/
theorem cornerFamilyDesc_lower
    (hl : ∀ (a : SimplexCategory.reedyOp.Latching n)
        (s : L.obj (SimplexCategory.reedyOp.latchingSource a)),
      F'.map (SimplexCategory.reedyOp.latchingArrow a) ≫ l
          (L.map (SimplexCategory.reedyOp.latchingArrow a) s) =
        inclusion F' L (SimplexCategory.reedyOp.latchingSource a) s ≫
          colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' L) n) a ≫
            CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
                (pushoutProduct i j) n t) :
    CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp (tensor F' L) n ≫
      cornerFamilyDesc (F' := F') (L := L) n l =
      CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
          (pushoutProduct i j) n t := by
  apply colimit.hom_ext
  intro a
  apply tensorCoefficient_hom_ext F' L (SimplexCategory.reedyOp.latchingSource a)
  intro s
  rw [← Category.assoc
    (colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' L) n) a)
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp (tensor F' L) n)
    (cornerFamilyDesc (F' := F') (L := L) n l), CategoryTheory.ReedyStructure.latchingMap_ι]
  rw [← Category.assoc (inclusion F' L (SimplexCategory.reedyOp.latchingSource a) s)
    ((tensor F' L).map (SimplexCategory.reedyOp.latchingArrow a))
    (cornerFamilyDesc (F' := F') (L := L) n l), inclusion_tensor_map,
    Category.assoc, cornerFamilyDesc_ι]
  exact hl a s

/-- The actual original finite family gives the complete actual native latching-corner lift. -/
def nativeCornerLiftOfCopies {B : C} (p : E ⟶ B) (b : (tensor F' L).obj n ⟶ B)
    (sq : CommSq t
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp (pushoutProduct i j)
        n) p b)
    (hc : ∀ s : L.obj n, i.app n ≫ l s = pushoutSourceNewCopy i j n s ≫
      CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i j) n t)
    (ho : ∀ k : K.obj n, l (j.app n k) = pushoutSourceOldCopy i j n k ≫
      CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i j) n t)
    (hl : ∀ (a : SimplexCategory.reedyOp.Latching n)
        (s : L.obj (SimplexCategory.reedyOp.latchingSource a)),
      F'.map (SimplexCategory.reedyOp.latchingArrow a) ≫ l
          (L.map (SimplexCategory.reedyOp.latchingArrow a) s) =
        inclusion F' L (SimplexCategory.reedyOp.latchingSource a) s ≫
          colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' L) n) a ≫
            CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
                (pushoutProduct i j) n t)
    (hr : ∀ s : L.obj n, l s ≫ p = inclusion F' L n s ≫ b) : sq.LiftStruct where
  l := cornerFamilyDesc (F' := F') (L := L) n l
  fac_left := by
    apply pushout.hom_ext
    · rw [← Category.assoc, CategoryTheory.ReedyStructure.latchingCorner_inl]
      exact cornerFamilyDesc_component i j n t l hc ho
    · rw [← Category.assoc, CategoryTheory.ReedyStructure.latchingCorner_inr]
      exact cornerFamilyDesc_lower i j n t l hl
  fac_right := by
    apply Sigma.hom_ext
    intro s
    change inclusion F' L n s ≫ cornerFamilyDesc (F' := F') (L := L) n l ≫ p = _
    rw [← Category.assoc, cornerFamilyDesc_ι]
    exact hr s

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-! # Original partial-factor coefficients in the actual tensor latching colimit -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]

/-- The complete original tensor latching cocone restricted along every original partial epi factor.
-/
def factorCopyCocone (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    Cocone (partialSourceRestriction F α) :=
  (Cocone.precompose (factorCopyTransformation F α)).obj
    ((colimit.cocone
        (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌))).whisker
      (SimplexCategory.PartialLatching.inclusion α))

/-- Every retained epi factor reads back the original coefficient and original residual tensor
label. -/
theorem factorCopyCocone_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (a : SimplexCategory.PartialLatching.Index α) :
    (factorCopyCocone F α).ι.app a =
      inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a) ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a.obj :=
  rfl

/-- The original partial coefficient colimit maps to the original tensor latching colimit. -/
def factorCopyColimitMap (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    colimit (partialSourceRestriction F α) ⟶
      colimit (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌)) :=
  colimit.desc _ (factorCopyCocone F α)

/-- Every original partial colimit injection keeps its original coefficient and residual simplex
label. -/
@[reassoc]
theorem factorCopyColimitMap_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (a : SimplexCategory.PartialLatching.Index α) :
    colimit.ι (partialSourceRestriction F α) a ≫ factorCopyColimitMap F α =
      inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a) ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a.obj :=
  colimit.ι_desc _ a

/-- Each actual original incoming epi recovers the original coefficient map at the unchanged
original tensor label. -/
@[reassoc]
theorem factorCopyColimitMap_ι_latchingMap (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (a : SimplexCategory.PartialLatching.Index α) :
    colimit.ι (partialSourceRestriction F α) a ≫ factorCopyColimitMap F α ≫
        CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
            (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌) =
      F.map (SimplexCategory.PartialLatching.arrow a) ≫
        inclusion F (Δ[d] : SSet.{v}) (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) := by
  rw [← Category.assoc, factorCopyColimitMap_ι, Category.assoc,
    CategoryTheory.ReedyStructure.latchingMap_ι]
  change inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a)
      ≫
      (tensor F (Δ[d] : SSet.{v})).map (SimplexCategory.PartialLatching.arrow a) = _
  rw [inclusion_tensor_map, factorLabel_arrow]

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-! # Original old boundary coefficient lifts inside the actual native corner datum -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  {F F' : SimplicialObject C} (i : F ⟶ F') (m d : ℕ) {E : C}
  (t : pushout
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      (pushout (tensorMap i (𝟙 (SSet.boundary.{v} d : SSet.{v})))
          (tensorMap (𝟙 F) (SSet.boundary.{v} d).ι)) (op ⦋m⦌))
    (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌))) ⟶ E)

/-- Each original boundary copy gives its unchanged original old coefficient lift datum. -/
def nativeOldCoefficientTop (k : (SSet.boundary.{v} d : SSet.{v}).obj (op ⦋m⦌)) :
    F'.obj (op ⦋m⦌) ⟶ E :=
  pushoutSourceOldCopy i (SSet.boundary.{v} d).ι (op ⦋m⦌) k ≫
    CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t

/-- Each original coefficient map retains the actual old/new source-copy relation in the corner
datum. -/
@[reassoc]
theorem nativeOldCoefficientTop_coefficient (k : (SSet.boundary.{v} d : SSet.{v}).obj (op ⦋m⦌)) :
    i.app (op ⦋m⦌) ≫ nativeOldCoefficientTop i m d t k =
      pushoutSourceNewCopy i (SSet.boundary.{v} d).ι (op ⦋m⦌)
          ((SSet.boundary.{v} d).ι.app (op ⦋m⦌) k) ≫
        CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  dsimp only [nativeOldCoefficientTop]
  rw [← Category.assoc, pushoutSourceCopy_relation]

/-- Every original old coefficient retains each original epi triangle into the actual lower target
datum. -/
@[reassoc]
theorem nativeOldCoefficientTop_naturality (a : SimplexCategory.reedyOp.Latching (op ⦋m⦌))
    (k : (SSet.boundary.{v} d : SSet.{v}).obj (SimplexCategory.reedyOp.latchingSource a)) :
    F'.map (SimplexCategory.reedyOp.latchingArrow a) ≫
        nativeOldCoefficientTop i m d t ((SSet.boundary.{v} d : SSet.{v}).map
          (SimplexCategory.reedyOp.latchingArrow a) k) =
      inclusion F' (Δ[d] : SSet.{v}) (SimplexCategory.reedyOp.latchingSource a)
          ((SSet.boundary.{v} d).ι.app (SimplexCategory.reedyOp.latchingSource a) k) ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a ≫
          CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
            (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  dsimp only [nativeOldCoefficientTop]
  rw [← Category.assoc, pushoutSourceOldCopy_naturality, Category.assoc,
    CategoryTheory.ReedyStructure.Shape.latchingCornerData_naturality,
        pushoutSourceOldCopy_map_assoc]

variable {B : C} (p : E ⟶ B)
  (b : (tensor F' (Δ[d] : SSet.{v})).obj (op ⦋m⦌) ⟶ B)
  (sq : CommSq t (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌)) p b)

include sq

/-- Every original old coefficient copy satisfies the actual original lower-right lift equation. -/
@[reassoc]
theorem nativeOldCoefficientTop_right (k : (SSet.boundary.{v} d : SSet.{v}).obj (op ⦋m⦌)) :
    nativeOldCoefficientTop i m d t k ≫ p =
      inclusion F' (Δ[d] : SSet.{v}) (op ⦋m⦌) ((SSet.boundary.{v} d).ι.app (op ⦋m⦌) k) ≫ b := by
  dsimp only [nativeOldCoefficientTop]
  rw [Category.assoc,
    (CategoryTheory.ReedyStructure.Shape.latchingCornerData_coefficientSquare
        SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t p b sq).w,
    pushoutSourceOldCopy_map_assoc]

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-! # Original partial corner data extracted from an actual native tensor boundary corner -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C]

/-- The whole original partial coefficient diagram is literally the proved partial-factor
restriction. -/
theorem partialSourceRestriction_eq_diagram (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    partialSourceRestriction F α = PartialDegeneracyLatching.diagram F α := rfl

variable [HasFiniteColimits C]

/-- The original partial-factor coefficient colimit maps into the original full tensor latching
object. -/
def nativePartialCopyMap (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    colimit (PartialDegeneracyLatching.diagram F α) ⟶
      colimit (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌)) :=
  factorCopyColimitMap F α

/-- Every original partial coefficient remains its original tensor label and latching injection. -/
@[reassoc]
theorem nativePartialCopyMap_ι (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (a : SimplexCategory.PartialLatching.Index α) :
    colimit.ι (PartialDegeneracyLatching.diagram F α) a ≫ nativePartialCopyMap F α =
      inclusion F (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a) ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a.obj :=
  factorCopyColimitMap_ι F α a

/-- The whole original partial map into a tensor coefficient is the original incoming tensor
degeneracy map. -/
@[reassoc]
theorem nativePartialCopyMap_latchingMap (F : SimplicialObject C) {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    nativePartialCopyMap F α ≫
        CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
            (tensor F (Δ[d] : SSet.{v})) (op ⦋m⦌) =
      PartialDegeneracyLatching.map F α ≫
        inclusion F (Δ[d] : SSet.{v}) (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, ← Category.assoc, PartialDegeneracyLatching.map_ι]
  exact (Category.assoc _ _ _).trans (factorCopyColimitMap_ι_latchingMap F α a)

variable {F F' : SimplicialObject C} (i : F ⟶ F') {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) {E : C}
  (t : pushout
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      (pushout (tensorMap i (𝟙 (SSet.boundary.{v} d : SSet.{v})))
          (tensorMap (𝟙 F) (SSet.boundary.{v} d).ι)) (op ⦋m⦌))
    (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌))) ⟶ E)

/-- The original source coefficient copy in a native corner datum. -/
def nativeNewPartialCoefficientTop : F.obj (op ⦋m⦌) ⟶ E :=
  pushoutSourceNewCopy i (SSet.boundary.{v} d).ι (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) ≫
    CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t

/-- The original partial target colimit in the native full lower corner datum. -/
def nativePartialLowerTop : colimit (PartialDegeneracyLatching.diagram F' α) ⟶ E :=
  nativePartialCopyMap F' α ≫ CategoryTheory.ReedyStructure.Shape.latchingCornerLower
      SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t

/-- Every original partial epi triangle commutes in the original extracted tensor corner datum. -/
@[reassoc]
theorem nativeNewPartialCoefficientTop_naturality (a : SimplexCategory.PartialLatching.Index α) :
    F.map (SimplexCategory.PartialLatching.arrow a) ≫ nativeNewPartialCoefficientTop i α t =
      i.app (SimplexCategory.PartialLatching.source a) ≫
        colimit.ι (PartialDegeneracyLatching.diagram F' α) a ≫ nativePartialLowerTop i α t := by
  dsimp only [nativeNewPartialCoefficientTop, nativePartialLowerTop]
  rw [← factorLabel_arrow α a, ← Category.assoc, pushoutSourceNewCopy_naturality, Category.assoc]
  dsimp only [SimplexCategory.PartialLatching.arrow]
  rw [CategoryTheory.ReedyStructure.Shape.latchingCornerData_naturality,
    pushoutSourceNewCopy_map_assoc, nativePartialCopyMap_ι_assoc]

/-- The complete original partial colimit datum retains the actual original pushout compatibility.
-/
theorem nativeNewPartialCoefficientTop_compatibility :
    PartialDegeneracyLatching.map F α ≫ nativeNewPartialCoefficientTop i α t =
      colimMap (PartialDegeneracyLatching.transformation i α) ≫ nativePartialLowerTop i α t := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, PartialDegeneracyLatching.map_ι, ← Category.assoc, ι_colimMap]
  rw [PartialDegeneracyLatching.transformation_app, Category.assoc]
  exact nativeNewPartialCoefficientTop_naturality i α t a

/-- The complete original extracted partial pushout datum. -/
def nativePartialTop :
    pushout (PartialDegeneracyLatching.map F α)
      (colimMap (PartialDegeneracyLatching.transformation i α)) ⟶ E :=
  pushout.desc (nativeNewPartialCoefficientTop i α t) (nativePartialLowerTop i α t)
    (nativeNewPartialCoefficientTop_compatibility i α t)

/-- The first original partial pushout leg reads back the unchanged source coefficient datum. -/
@[reassoc]
theorem nativePartialTop_inl :
    pushout.inl (PartialDegeneracyLatching.map F α)
        (colimMap (PartialDegeneracyLatching.transformation i α)) ≫ nativePartialTop i α t =
      nativeNewPartialCoefficientTop i α t := pushout.inl_desc _ _ _

/-- The second original partial pushout leg reads back the unchanged full partial target datum. -/
@[reassoc]
theorem nativePartialTop_inr :
    pushout.inr (PartialDegeneracyLatching.map F α)
        (colimMap (PartialDegeneracyLatching.transformation i α)) ≫ nativePartialTop i α t =
      nativePartialLowerTop i α t := pushout.inr_desc _ _ _

section Squares

variable {B : C} (p : E ⟶ B)
  (b : (tensor F' (Δ[d] : SSet.{v})).obj (op ⦋m⦌) ⟶ B)
  (sq : CommSq t (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌)) p b)

include sq

/-- The original extracted coefficient square of each original residual simplex. -/
theorem nativeNewPartialCoefficientSquare :
    CommSq (nativeNewPartialCoefficientTop i α t) (i.app (op ⦋m⦌)) p
      (inclusion F' (Δ[d] : SSet.{v}) (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) ≫ b) := by
  constructor
  dsimp only [nativeNewPartialCoefficientTop]
  rw [Category.assoc,
    (CategoryTheory.ReedyStructure.Shape.latchingCornerData_coefficientSquare
        SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t p b sq).w,
    pushoutSourceNewCopy_map_assoc]

/-- The original extracted partial-target datum has the original whole lower-square equation. -/
@[reassoc]
theorem nativePartialLowerSquare :
    nativePartialLowerTop i α t ≫ p = PartialDegeneracyLatching.map F' α ≫
      inclusion F' (Δ[d] : SSet.{v}) (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) ≫ b := by
  dsimp only [nativePartialLowerTop]
  rw [Category.assoc, CategoryTheory.ReedyStructure.Shape.latchingCornerData_lowerSquare
    SimplexCategory.reedyOp (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t p b sq,
    ← Category.assoc, nativePartialCopyMap_latchingMap, Category.assoc]

/-- The actual native tensor-corner square induces the actual original partial-corner square. -/
theorem nativePartialSquare :
    CommSq (nativePartialTop i α t) (PartialDegeneracyLatching.corner i α) p
      (inclusion F' (Δ[d] : SSet.{v}) (op ⦋m⦌) (SSet.stdSimplex.objEquiv.symm α) ≫ b) := by
  constructor
  apply pushout.hom_ext
  · rw [nativePartialTop_inl_assoc, PartialDegeneracyLatching.corner_inl_assoc]
    exact (nativeNewPartialCoefficientSquare i α t p b sq).w
  · rw [nativePartialTop_inr_assoc, PartialDegeneracyLatching.corner_inr_assoc]
    exact nativePartialLowerSquare i α t p b sq

end Squares

/-- An actual partial lift retains the original coefficient lift triangle. -/
theorem nativePartialLift_coefficient
    (l : F'.obj (op ⦋m⦌) ⟶ E)
    (hl : PartialDegeneracyLatching.corner i α ≫ l = nativePartialTop i α t) :
    i.app (op ⦋m⦌) ≫ l = nativeNewPartialCoefficientTop i α t := by
  have h := congrArg (fun f => pushout.inl (PartialDegeneracyLatching.map F α)
    (colimMap (PartialDegeneracyLatching.transformation i α)) ≫ f) hl
  simpa only [PartialDegeneracyLatching.corner_inl_assoc, nativePartialTop_inl] using h

/-- An actual partial lift retains the original whole partial-target lift triangle. -/
theorem nativePartialLift_lower
    (l : F'.obj (op ⦋m⦌) ⟶ E)
    (hl : PartialDegeneracyLatching.corner i α ≫ l = nativePartialTop i α t) :
    PartialDegeneracyLatching.map F' α ≫ l = nativePartialLowerTop i α t := by
  have h := congrArg (fun f => pushout.inr (PartialDegeneracyLatching.map F α)
    (colimMap (PartialDegeneracyLatching.transformation i α)) ≫ f) hl
  simpa only [PartialDegeneracyLatching.corner_inr_assoc, nativePartialTop_inr] using h

/-- Every original partial epi leg retains the original target-copy lift equation. -/
theorem nativePartialLift_lower_ι
    (l : F'.obj (op ⦋m⦌) ⟶ E)
    (hl : PartialDegeneracyLatching.corner i α ≫ l = nativePartialTop i α t)
    (a : SimplexCategory.PartialLatching.Index α) :
    F'.map (SimplexCategory.PartialLatching.arrow a) ≫ l =
      inclusion F' (Δ[d] : SSet.{v}) (SimplexCategory.PartialLatching.source a) (factorLabel α a) ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a.obj ≫
          CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
            (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  have h := congrArg (fun f => colimit.ι (PartialDegeneracyLatching.diagram F' α) a ≫ f)
    (nativePartialLift_lower i α t l hl)
  simpa only [PartialDegeneracyLatching.map_ι_assoc, nativePartialLowerTop,
    nativePartialCopyMap_ι_assoc] using h

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Actual old boundary copies and original partial lifts form the complete native lift

The finite family consists of the actual old coefficient datum at every
boundary label and an actual original partial-corner lift at each new label.
All original source, epi and target triangles are retained before the native
corner LiftStruct is assembled. No model preservation assertion is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

/-- Every original new standard simplex retains its actual label outside the original boundary. -/
abbrev NewBoundaryLabel (m d : ℕ) :=
  {s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌) // s ∉ (SSet.boundary.{v} d).obj (op ⦋m⦌)}

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  {F F' : SimplicialObject C} (i : F ⟶ F') (m d : ℕ) {E B : C}
  (t : pushout
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      (pushout (tensorMap i (𝟙 (SSet.boundary.{v} d : SSet.{v})))
          (tensorMap (𝟙 F) (SSet.boundary.{v} d).ι)) (op ⦋m⦌))
    (colimMap (SimplexCategory.reedyOp.latchingTransformation
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌))) ⟶ E)
  (p : E ⟶ B) (b : (tensor F' (Δ[d] : SSet.{v})).obj (op ⦋m⦌) ⟶ B)
  (sq : CommSq t (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
    (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌)) p b)
  (lifts : ∀ s : NewBoundaryLabel.{v} m d,
    (nativePartialSquare i (SSet.stdSimplex.objEquiv s.val) t p b sq).LiftStruct)

/-- The complete original coefficient family, using actual old copies and actual partial lifts. -/
def nativeBoundaryFamily (s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌)) : F'.obj (op ⦋m⦌) ⟶ E := by
  classical
  exact if hs : s ∈ (SSet.boundary.{v} d).obj (op ⦋m⦌) then nativeOldCoefficientTop i m d t ⟨s, hs⟩
    else (lifts ⟨s, hs⟩).l

/-- Every original old label reads back its actual old coefficient map. -/
theorem nativeBoundaryFamily_of_mem (s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌))
    (hs : s ∈ (SSet.boundary.{v} d).obj (op ⦋m⦌)) :
    nativeBoundaryFamily i m d t p b sq lifts s = nativeOldCoefficientTop i m d t ⟨s, hs⟩ := by
  classical
  dsimp only [nativeBoundaryFamily]
  split
  · rfl
  · next h => exact (h hs).elim

/-- Every original new label reads back its actual original partial lift. -/
theorem nativeBoundaryFamily_of_not_mem (s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌))
    (hs : s ∉ (SSet.boundary.{v} d).obj (op ⦋m⦌)) :
    nativeBoundaryFamily i m d t p b sq lifts s = (lifts ⟨s, hs⟩).l := by
  classical
  dsimp only [nativeBoundaryFamily]
  split
  · next h => exact (hs h).elim
  · rfl

/-- Every original source coefficient copy retains the actual coefficient triangle. -/
theorem nativeBoundaryFamily_coefficient (s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌)) :
    i.app (op ⦋m⦌) ≫ nativeBoundaryFamily i m d t p b sq lifts s =
      pushoutSourceNewCopy i (SSet.boundary.{v} d).ι (op ⦋m⦌) s ≫
        CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  classical
  by_cases hs : s ∈ (SSet.boundary.{v} d).obj (op ⦋m⦌)
  · rw [nativeBoundaryFamily_of_mem i m d t p b sq lifts s hs]
    exact nativeOldCoefficientTop_coefficient i m d t ⟨s, hs⟩
  · rw [nativeBoundaryFamily_of_not_mem i m d t p b sq lifts s hs]
    have h := nativePartialLift_coefficient i (SSet.stdSimplex.objEquiv s) t
      (lifts ⟨s, hs⟩).l (lifts ⟨s, hs⟩).fac_left
    simpa only [nativeNewPartialCoefficientTop, Equiv.symm_apply_apply] using h

/-- Every original boundary-index coefficient copy retains the actual old target triangle. -/
theorem nativeBoundaryFamily_old (k : (SSet.boundary.{v} d : SSet.{v}).obj (op ⦋m⦌)) :
    nativeBoundaryFamily i m d t p b sq lifts ((SSet.boundary.{v} d).ι.app (op ⦋m⦌) k) =
      pushoutSourceOldCopy i (SSet.boundary.{v} d).ι (op ⦋m⦌) k ≫
        CategoryTheory.ReedyStructure.Shape.latchingCornerTop SimplexCategory.reedyOp
          (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  change nativeBoundaryFamily i m d t p b sq lifts k.val = nativeOldCoefficientTop i m d t k
  exact nativeBoundaryFamily_of_mem i m d t p b sq lifts k.val k.property

/-- Every original finite coefficient copy retains the actual lower-right lift triangle. -/
theorem nativeBoundaryFamily_right (s : (Δ[d] : SSet.{v}).obj (op ⦋m⦌)) :
    nativeBoundaryFamily i m d t p b sq lifts s ≫ p = inclusion F' (Δ[d] : SSet.{v}) (op ⦋m⦌) s ≫ b
        := by
  classical
  by_cases hs : s ∈ (SSet.boundary.{v} d).obj (op ⦋m⦌)
  · rw [nativeBoundaryFamily_of_mem i m d t p b sq lifts s hs]
    exact nativeOldCoefficientTop_right i m d t p b sq ⟨s, hs⟩
  · rw [nativeBoundaryFamily_of_not_mem i m d t p b sq lifts s hs]
    simpa only [Equiv.symm_apply_apply] using (lifts ⟨s, hs⟩).fac_right

/-- Every original incoming epi operator retains the exact original lower target lift equation. -/
theorem nativeBoundaryFamily_lower (a : SimplexCategory.reedyOp.Latching (op ⦋m⦌))
    (s : (Δ[d] : SSet.{v}).obj (SimplexCategory.reedyOp.latchingSource a)) :
    F'.map (SimplexCategory.reedyOp.latchingArrow a) ≫
        nativeBoundaryFamily i m d t p b sq lifts
            ((Δ[d] : SSet.{v}).map (SimplexCategory.reedyOp.latchingArrow a) s) =
      inclusion F' (Δ[d] : SSet.{v}) (SimplexCategory.reedyOp.latchingSource a) s ≫
        colimit.ι (SimplexCategory.reedyOp.latchingDiagram (tensor F' (Δ[d] : SSet.{v})) (op ⦋m⦌))
            a ≫
          CategoryTheory.ReedyStructure.Shape.latchingCornerLower SimplexCategory.reedyOp
            (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌) t := by
  classical
  let _ : Epi (SimplexCategory.reedyOp.latchingArrow a).unop :=
    (SimplexCategory.reedyOp_direct _).1 a.obj.hom.property
  by_cases hs : s ∈ (SSet.boundary.{v} d).obj (SimplexCategory.reedyOp.latchingSource a)
  · have ht := (simplex_boundary_epi_map_iff d (SimplexCategory.reedyOp.latchingArrow a) s).2 hs
    rw [nativeBoundaryFamily_of_mem i m d t p b sq lifts _ ht]
    have hk : (⟨(Δ[d] : SSet.{v}).map (SimplexCategory.reedyOp.latchingArrow a) s, ht⟩ :
        (SSet.boundary.{v} d : SSet.{v}).obj (op ⦋m⦌)) =
      (SSet.boundary.{v} d : SSet.{v}).map (SimplexCategory.reedyOp.latchingArrow a) ⟨s, hs⟩ :=
      Subtype.ext rfl
    rw [hk]
    exact nativeOldCoefficientTop_naturality i m d t a ⟨s, hs⟩
  · have ht : (Δ[d] : SSet.{v}).map (SimplexCategory.reedyOp.latchingArrow a) s ∉
        (SSet.boundary.{v} d).obj (op ⦋m⦌) :=
      fun h => hs ((simplex_boundary_epi_map_iff d (SimplexCategory.reedyOp.latchingArrow a) s).1 h)
    rw [nativeBoundaryFamily_of_not_mem i m d t p b sq lifts _ ht]
    let z := (Δ[d] : SSet.{v}).map (SimplexCategory.reedyOp.latchingArrow a) s
    let α := SSet.stdSimplex.objEquiv z
    let aα : SimplexCategory.PartialLatching.Index α :=
      ⟨a, ⟨SSet.stdSimplex.objEquiv s, rfl⟩⟩
    have hf : factorLabel.{v} α aα = s := by
      have h := SimplexCategory.PartialLatching.factor_unique α aα (SSet.stdSimplex.objEquiv s) rfl
      exact (congrArg SSet.stdSimplex.objEquiv.symm h.symm).trans
        (SSet.stdSimplex.objEquiv.symm_apply_apply s)
    have h := nativePartialLift_lower_ι i α t (lifts ⟨z, ht⟩).l (lifts ⟨z, ht⟩).fac_left aα
    simpa only
        [hf, aα, z, SimplexCategory.PartialLatching.source, SimplexCategory.PartialLatching.arrow]
        using h

/-- Actual old coefficient data and actual original partial lifts give the complete native corner
lift. -/
def nativeBoundaryCornerLiftFromPartial : sq.LiftStruct :=
  nativeCornerLiftOfCopies i (SSet.boundary.{v} d).ι (op ⦋m⦌) t
    (nativeBoundaryFamily i m d t p b sq lifts) p b sq
    (nativeBoundaryFamily_coefficient i m d t p b sq lifts)
    (nativeBoundaryFamily_old i m d t p b sq lifts)
    (nativeBoundaryFamily_lower i m d t p b sq lifts)
    (nativeBoundaryFamily_right i m d t p b sq lifts)

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end

section



/-!
# Actual original finite boundary tensor Reedy cofibration laws

Every partial lift is produced internally by the actual source model weak
factorization system and the proved original partial-degeneracy corner law.
The original finite native lift assembler gives the complete original
latching-corner lift. All dimensions and all original boundary labels are
retained; no PP, partial-preservation, model, frame or SM7 outcome is input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial
open HomotopicalAlgebra.FiniteResolutionTensor

namespace HomotopicalAlgebra.ReedyFiniteTensorGeometry

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Every original standard-boundary tensor PP has its actual Reedy cofibration corner at every
dimension. -/
theorem nativeBoundaryPushoutProduct_corner_cofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : ∀ j, cofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    (d m : ℕ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌)) := by
  rw [← trivialFibrations_llp]
  intro E B p hp
  refine ⟨fun {t b} sq => ?_⟩
  let lifts : ∀ s : NewBoundaryLabel.{v} m d,
      (nativePartialSquare i (SSet.stdSimplex.objEquiv s.val) t p b sq).LiftStruct := fun s => by
    let _ : Epi (SSet.stdSimplex.objEquiv s.val) := simplex_epi_of_not_boundary d (op ⦋m⦌) s.val
        s.property
    let _ := MorphismProperty.hasLiftingProperty_of_wfs
      (PartialDegeneracyLatching.corner i (SSet.stdSimplex.objEquiv s.val)) p
      (PartialDegeneracyLatching.corner_cofibration i hi (SSet.stdSimplex.objEquiv s.val)) hp
    exact { l := (nativePartialSquare i (SSet.stdSimplex.objEquiv s.val) t p b sq).lift }
  exact CommSq.HasLift.mk' (nativeBoundaryCornerLiftFromPartial i m d t p b sq lifts)

/-- Every original standard-boundary tensor PP has its actual Reedy trivial corner from genuine
source trivial data. -/
theorem nativeBoundaryPushoutProduct_corner_trivialCofibration {F F' : SimplicialObject C}
    (i : F ⟶ F')
    (hi : ∀ j, trivialCofibrations C
        (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp i j))
    (d m : ℕ) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp
      (pushoutProduct i (SSet.boundary.{v} d).ι) (op ⦋m⦌)) := by
  rw [← fibrations_llp]
  intro E B p hp
  refine ⟨fun {t b} sq => ?_⟩
  let lifts : ∀ s : NewBoundaryLabel.{v} m d,
      (nativePartialSquare i (SSet.stdSimplex.objEquiv s.val) t p b sq).LiftStruct := fun s => by
    let _ : Epi (SSet.stdSimplex.objEquiv s.val) := simplex_epi_of_not_boundary d (op ⦋m⦌) s.val
        s.property
    let _ := MorphismProperty.hasLiftingProperty_of_wfs
      (PartialDegeneracyLatching.corner i (SSet.stdSimplex.objEquiv s.val)) p
      (PartialDegeneracyLatching.corner_trivialCofibration i hi (SSet.stdSimplex.objEquiv s.val)) hp
    exact { l := (nativePartialSquare i (SSet.stdSimplex.objEquiv s.val) t p b sq).lift }
  exact CommSq.HasLift.mk' (nativeBoundaryCornerLiftFromPartial i m d t p b sq lifts)

/-- The whole native finite boundary PP retains the actual original Reedy cofibration class. -/
theorem nativeBoundaryPushoutProduct_reedyCofibration {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) i)
    (d : ℕ) : CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C)
      (pushoutProduct i (SSet.boundary.{v} d).ι) :=
  fun n => nativeBoundaryPushoutProduct_corner_cofibration i hi d n.unop.len

/-- The whole native finite boundary PP retains the actual original Reedy trivial class. -/
theorem nativeBoundaryPushoutProduct_reedyTrivialCofibration {F F' : SimplicialObject C}
    (i : F ⟶ F')
    (hi : CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp
        (trivialCofibrations C) i)
    (d : ℕ) : CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp
        (trivialCofibrations C)
      (pushoutProduct i (SSet.boundary.{v} d).ι) :=
  fun n => nativeBoundaryPushoutProduct_corner_trivialCofibration i hi d n.unop.len

/-- Genuine source Reedy cofibration and source weak components produce the unchanged native
boundary PP
trivial class. -/
theorem nativeBoundaryPushoutProduct_reedyTrivialCofibration_of_cofibration_weak
    {F F' : SimplicialObject C} (i : F ⟶ F')
    (hi : CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) i)
    (hw : ∀ j, weakEquivalences C (i.app j)) (d : ℕ) :
    CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C)
      (pushoutProduct i (SSet.boundary.{v} d).ι) :=
  nativeBoundaryPushoutProduct_reedyTrivialCofibration i
    (ReedyModel.latchingCorner_trivialCofibration_of_cofibration_weak SimplexCategory.reedyOp i hi
        hw) d

end HomotopicalAlgebra.ReedyFiniteTensorGeometry

end
end
end
