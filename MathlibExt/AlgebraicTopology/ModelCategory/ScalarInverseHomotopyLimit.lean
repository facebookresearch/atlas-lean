/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedDiagramConstructions

/-!
# The actual scalar homotopy limit of an inverse sequence

Evaluation at the original zero stage is left adjoint to the constant diagram
on the original inverse natural-number index. The constructed scalar injective
model makes this pair Quillen. Hence an original fibrant scalar gives a fibrant
constant diagram, and its actual original limit-to-homotopy-limit comparison is
weak. These maps are used for the inverse mapping diagrams of module telescopes.
-/

set_option autoImplicit false
noncomputable section

universe u v z

open CategoryTheory Limits Opposite MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.ScalarInverseHomotopyLimit

/-- The unchanged original zero stage in the inverse sequence. -/
abbrev zero : ℕᵒᵖ := op 0

/-- Every original inverse stage has its actual original arrow to zero. -/
def toZero (n : ℕᵒᵖ) : n ⟶ zero := (homOfLE (Nat.zero_le n.unop)).op

variable {C : Type u} [Category.{v} C]

/-- Evaluation at the original zero stage of the original inverse diagram. -/
def evaluationAtZero : (ℕᵒᵖ ⥤ C) ⥤ C := (evaluation ℕᵒᵖ C).obj zero

/-- The original zero-stage arrow extends along all the original inverse maps. -/
def extendZero (F : ℕᵒᵖ ⥤ C) (X : C) (f : F.obj zero ⟶ X) :
    F ⟶ (Functor.const ℕᵒᵖ).obj X where
  app n := F.map (toZero n) ≫ f
  naturality n m a := by
    change F.map a ≫ (F.map (toZero m) ≫ f) = (F.map (toZero n) ≫ f) ≫ 𝟙 X
    rw [Category.comp_id, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun q => F.map q ≫ f) (Subsingleton.elim _ _)

/-- The actual zero-stage value recovers the original input arrow. -/
theorem extendZero_zero (F : ℕᵒᵖ ⥤ C) (X : C) (f : F.obj zero ⟶ X) :
    (extendZero F X f).app zero = f := by
  change F.map (toZero zero) ≫ f = f
  have h : toZero zero = 𝟙 zero := Subsingleton.elim _ _
  rw [h, F.map_id, Category.id_comp]

/-- Every original constant-diagram map is recovered from the same zero-stage map. -/
theorem extendZero_recovery (F : ℕᵒᵖ ⥤ C) (X : C)
    (f : F ⟶ (Functor.const ℕᵒᵖ).obj X) :
    extendZero F X (f.app zero) = f := by
  apply NatTrans.ext
  funext n
  exact (f.naturality (toZero n)).trans (Category.comp_id _)

/-- Both full original Hom functions of evaluation and the constant diagram. -/
def zeroHomEquiv (F : ℕᵒᵖ ⥤ C) (X : C) :
    (F.obj zero ⟶ X) ≃ (F ⟶ (Functor.const ℕᵒᵖ).obj X) where
  toFun := extendZero F X
  invFun f := f.app zero
  left_inv := extendZero_zero F X
  right_inv := extendZero_recovery F X

/-- The actual evaluation/constant adjunction keeps every original inverse-index map. -/
def evaluationConstAdjunction : evaluationAtZero (C := C) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := zeroHomEquiv
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun f g => by
        apply NatTrans.ext
        funext n
        exact (Category.assoc _ _ _).symm }

/-- The constant cone retains its actual identity projection at every stage. -/
def constantCone (X : C) : Cone ((Functor.const ℕᵒᵖ).obj X) where
  pt := X
  π := { app _ := 𝟙 X, naturality _ _ _ := by simp }

/-- The original zero-stage projection proves the full constant-cone universal property. -/
def constantConeIsLimit (X : C) : IsLimit (constantCone X) where
  lift s := s.π.app zero
  fac s n := by
    change s.π.app zero ≫ 𝟙 X = s.π.app n
    have h := s.π.naturality (toZero n)
    change 𝟙 s.pt ≫ s.π.app zero = s.π.app n ≫ 𝟙 X at h
    exact (Category.comp_id (s.π.app zero)).trans
      ((Category.id_comp (s.π.app zero)).symm.trans
        (h.trans (Category.comp_id (s.π.app n))))
  uniq s f hf := by
    have h := hf zero
    change f ≫ 𝟙 X = s.π.app zero at h
    exact (Category.comp_id f).symm.trans h

/-- The chosen limit is compared with the original constant object by its actual cone maps.
The constant cone itself supplies this limit for the original connected index. -/
def constantLimitIso (X : C) :
    limit ((Functor.const ℕᵒᵖ).obj X) ≅ X :=
  (limit.isLimit ((Functor.const ℕᵒᵖ).obj X)).conePointUniqueUpToIso (constantConeIsLimit X)

/-- The inverse constant-limit map preserves every original identity cone leg. -/
@[reassoc]
theorem constantLimitIso_inv_π (X : C) (n : ℕᵒᵖ) :
    (constantLimitIso X).inv ≫ limit.π ((Functor.const ℕᵒᵖ).obj X) n = 𝟙 X :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (limit.isLimit ((Functor.const ℕᵒᵖ).obj X)) (constantConeIsLimit X) n

/-- Every actual scalar arrow retains the same original inverse constant-limit map. -/
theorem constantLimitIso_inv_naturality [HasLimitsOfShape ℕᵒᵖ C]
    {X Y : C} (f : X ⟶ Y) :
    f ≫ (constantLimitIso Y).inv =
      (constantLimitIso X).inv ≫ lim.map ((Functor.const ℕᵒᵖ).map f) := by
  apply limit.hom_ext
  intro n
  calc
    _ = f := by rw [Category.assoc, constantLimitIso_inv_π, Category.comp_id]
    _ = _ := by
      symm
      rw [Category.assoc, limit.map_π, ← Category.assoc, constantLimitIso_inv_π,
        Functor.const_map_app, Category.id_comp]

section Scalar

variable (X : SSet.{z})

/-- The actual scalar injective cofibrations make original evaluation at zero left Quillen. -/
theorem evaluationConst_isQuillen :
    letI := DerivedDiagramConstructions.scalarModel.{0, 0, z} ℕᵒᵖ
    (evaluationConstAdjunction (C := SSet.{z})).IsQuillenAdjunction := by
  let _ := DerivedDiagramConstructions.scalarModel.{0, 0, z} ℕᵒᵖ
  refine { preservesCofibrations := ?_, preservesTrivialCofibrations := ?_ }
  · intro F G f hf
    rw [DerivedDiagramConstructions.scalarModel_cofibrations.{0, 0, z} ℕᵒᵖ] at hf
    exact hf zero
  · intro F G f hf
    rw [DerivedDiagramConstructions.scalarModel_trivialCofibrations.{0, 0, z} ℕᵒᵖ] at hf
    exact hf zero

/-- Fibrancy of the original scalar supplies fibrancy of its actual constant inverse diagram. -/
theorem constant_isFibrant [IsFibrant X] :
    letI := DerivedDiagramConstructions.scalarModel.{0, 0, z} ℕᵒᵖ
    IsFibrant ((Functor.const ℕᵒᵖ).obj X) := by
  let _ := DerivedDiagramConstructions.scalarModel.{0, 0, z} ℕᵒᵖ
  let _ : (evaluationConstAdjunction (C := SSet.{z})).IsQuillenAdjunction :=
    evaluationConst_isQuillen
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := evaluationConstAdjunction (C := SSet.{z})) inferInstance

/-- The actual original constant object maps through its chosen limit to the scalar homotopy limit. -/
def constantComparison : X ⟶
    (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).obj
      ((Functor.const ℕᵒᵖ).obj X) :=
  (constantLimitIso X).inv ≫
    (DerivedDiagramConstructions.scalarLimitComparison.{0, 0, z} ℕᵒᵖ).app
      ((Functor.const ℕᵒᵖ).obj X)

/-- The actual constant comparison is natural in the original scalar arrow. -/
theorem constantComparison_naturality {Y : SSet.{z}} (f : X ⟶ Y) :
    f ≫ constantComparison Y = constantComparison X ≫
      (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map
        ((Functor.const ℕᵒᵖ).map f) := by
  let H := DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ
  let c := DerivedDiagramConstructions.scalarLimitComparison.{0, 0, z} ℕᵒᵖ
  let a := (Functor.const ℕᵒᵖ).map f
  change f ≫ ((constantLimitIso Y).inv ≫ c.app ((Functor.const ℕᵒᵖ).obj Y)) =
    ((constantLimitIso X).inv ≫ c.app ((Functor.const ℕᵒᵖ).obj X)) ≫ H.map a
  calc
    _ = (f ≫ (constantLimitIso Y).inv) ≫ c.app ((Functor.const ℕᵒᵖ).obj Y) :=
      (Category.assoc _ _ _).symm
    _ = ((constantLimitIso X).inv ≫ lim.map a) ≫ c.app ((Functor.const ℕᵒᵖ).obj Y) :=
      congrArg (· ≫ c.app ((Functor.const ℕᵒᵖ).obj Y)) (constantLimitIso_inv_naturality f)
    _ = (constantLimitIso X).inv ≫
        (c.app ((Functor.const ℕᵒᵖ).obj X) ≫ H.map a) :=
      (Category.assoc _ _ _).trans
        (congrArg ((constantLimitIso X).inv ≫ ·) (c.naturality a))
    _ = _ := (Category.assoc _ _ _).symm

/-- The original constant comparison is weak, derived from the actual scalar Quillen pair. -/
theorem constantComparison_weak [IsFibrant X] :
    weakEquivalences SSet.{z} (constantComparison X) := by
  have h := DerivedDiagramConstructions.scalarLimitComparison_weak.{0, 0, z} ℕᵒᵖ
    ((Functor.const ℕᵒᵖ).obj X) (constant_isFibrant X)
  exact (weakEquivalences SSet.{z}).comp_mem _ _
    (HomotopicalAlgebra.mem_weakEquivalences (f := (constantLimitIso X).inv)) h

end Scalar

section InverseDiagram

variable (F : ℕᵒᵖ ⥤ SSet.{z})

/-- The original inverse diagram maps to its original zero value through its
actual original prefix arrows. -/
def toConstantZero : F ⟶ (Functor.const ℕᵒᵖ).obj (F.obj zero) :=
  extendZero F (F.obj zero) (𝟙 (F.obj zero))

/-- Every inverse stage retains its original actual map to zero. -/
theorem toConstantZero_app (n : ℕᵒᵖ) :
    (toConstantZero F).app n = F.map (toZero n) :=
  Category.comp_id _

/-- The original zero-stage component is exactly the original identity. -/
theorem toConstantZero_zero :
    (toConstantZero F).app zero = 𝟙 (F.obj zero) := extendZero_zero _ _ _

/-- The whole map of original inverse diagrams commutes with their actual
original zero-prefix maps. -/
theorem toConstantZero_naturality {G : ℕᵒᵖ ⥤ SSet.{z}} (a : F ⟶ G) :
    a ≫ toConstantZero G = toConstantZero F ≫ (Functor.const ℕᵒᵖ).map (a.app zero) := by
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, Functor.const_map_app, toConstantZero_app] using
    (a.naturality (toZero n)).symm

variable (hSucc : ∀ n : ℕ, weakEquivalences SSet.{z}
  (F.map ((homOfLE (Nat.le_succ n)).op)))

include hSucc in
/-- Actual weak successor maps give weak maps at every original zero-prefix. -/
theorem prefix_weak (n : ℕ) :
    weakEquivalences SSet.{z} (F.map (toZero (op n))) := by
  induction n with
  | zero =>
      have h : toZero (op 0) = 𝟙 (op 0) := Subsingleton.elim _ _
      have hmap : F.map (toZero (op 0)) = 𝟙 (F.obj (op 0)) :=
        (congrArg F.map h).trans (F.map_id (op 0))
      exact hmap.symm ▸ HomotopicalAlgebra.mem_weakEquivalences (f := 𝟙 (F.obj (op 0)))
  | succ n ih =>
      have h : F.map (toZero (op (n + 1))) =
          F.map ((homOfLE (Nat.le_succ n)).op) ≫ F.map (toZero (op n)) := by
        rw [← F.map_comp]
        exact congrArg F.map (Subsingleton.elim _ _)
      rw [h]
      exact (weakEquivalences SSet.{z}).comp_mem _ _ (hSucc n) ih

include hSucc in
/-- The map to the original constant zero diagram is weak at every actual stage. -/
theorem toConstantZero_weak (n : ℕᵒᵖ) :
    weakEquivalences SSet.{z} ((toConstantZero F).app n) := by
  rw [toConstantZero_app]
  exact prefix_weak F hSucc n.unop

/-- The original inverse mapping diagram induces the actual scalar
homotopy-limit map to its original zero diagram. -/
def limitToZero :
    (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).obj F ⟶
      (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).obj
        ((Functor.const ℕᵒᵖ).obj (F.obj zero)) :=
  (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map (toConstantZero F)

/-- The original inverse-diagram arrow retains its entire homotopy-limit square. -/
theorem limitToZero_naturality {G : ℕᵒᵖ ⥤ SSet.{z}} (a : F ⟶ G) :
    (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map a ≫ limitToZero G =
      limitToZero F ≫
        (DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map
          ((Functor.const ℕᵒᵖ).map (a.app zero)) := by
  let H := DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ
  change H.map a ≫ H.map (toConstantZero G) =
    H.map (toConstantZero F) ≫ H.map ((Functor.const ℕᵒᵖ).map (a.app zero))
  rw [← H.map_comp, toConstantZero_naturality, H.map_comp]

include hSucc in
/-- The original successor hypotheses derive weakness of that actual
homotopy-limit map; no limit-equivalence outcome is assumed. -/
theorem limitToZero_weak : weakEquivalences SSet.{z} (limitToZero F) :=
  DerivedDiagramConstructions.scalarHomotopyLimit_map_weak.{0, 0, z} ℕᵒᵖ
    (toConstantZero F) (toConstantZero_weak F hSucc)

variable [IsFibrant (F.obj zero)]

/-- The actual two weak span maps identify the original inverse homotopy
limit with its original zero scalar in the genuine scalar homotopy category. -/
def comparisonToZero :
    DerivedDiagramConstructions.scalarProjection.{z}.obj
        ((DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).obj F) ≅
      DerivedDiagramConstructions.scalarProjection.{z}.obj (F.obj zero) := by
  let P := DerivedDiagramConstructions.scalarProjection.{z}
  let _ : IsIso (P.map (limitToZero F)) :=
    Localization.inverts P (weakEquivalences SSet.{z}) _ (limitToZero_weak F hSucc)
  let _ : IsIso (P.map (constantComparison (F.obj zero))) :=
    Localization.inverts P (weakEquivalences SSet.{z}) _ (constantComparison_weak (F.obj zero))
  exact asIso (P.map (limitToZero F)) ≪≫ (asIso (P.map (constantComparison (F.obj zero)))).symm

/-- The scalar comparison retains its exact original span legs. -/
theorem comparisonToZero_span :
    (comparisonToZero F hSucc).hom ≫
        DerivedDiagramConstructions.scalarProjection.{z}.map (constantComparison (F.obj zero)) =
      DerivedDiagramConstructions.scalarProjection.{z}.map (limitToZero F) := by
  let P := DerivedDiagramConstructions.scalarProjection.{z}
  let _ : IsIso (P.map (limitToZero F)) :=
    Localization.inverts P (weakEquivalences SSet.{z}) _ (limitToZero_weak F hSucc)
  let _ : IsIso (P.map (constantComparison (F.obj zero))) :=
    Localization.inverts P (weakEquivalences SSet.{z}) _ (constantComparison_weak (F.obj zero))
  change (P.map (limitToZero F) ≫ inv (P.map (constantComparison (F.obj zero)))) ≫
      P.map (constantComparison (F.obj zero)) = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Both original zero-span maps retain the full natural comparison for an
actual arrow of weak inverse diagrams. -/
theorem comparisonToZero_naturality {G : ℕᵒᵖ ⥤ SSet.{z}} [IsFibrant (G.obj zero)]
    (hG : ∀ n : ℕ, weakEquivalences SSet.{z} (G.map ((homOfLE (Nat.le_succ n)).op)))
    (a : F ⟶ G) :
    DerivedDiagramConstructions.scalarProjection.{z}.map
        ((DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map a) ≫
      (comparisonToZero G hG).hom =
      (comparisonToZero F hSucc).hom ≫
        DerivedDiagramConstructions.scalarProjection.{z}.map (a.app zero) := by
  let P := DerivedDiagramConstructions.scalarProjection.{z}
  let H := DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ
  let _ : IsIso (P.map (constantComparison (G.obj zero))) :=
    Localization.inverts P (weakEquivalences SSet.{z}) _ (constantComparison_weak (G.obj zero))
  have hl : P.map (H.map a) ≫ P.map (limitToZero G) =
      P.map (limitToZero F) ≫ P.map (H.map ((Functor.const ℕᵒᵖ).map (a.app zero))) :=
    (P.map_comp _ _).symm.trans
      ((P.congr_map (limitToZero_naturality F a)).trans (P.map_comp _ _))
  have hc : P.map (constantComparison (F.obj zero)) ≫
      P.map (H.map ((Functor.const ℕᵒᵖ).map (a.app zero))) =
        P.map (a.app zero) ≫ P.map (constantComparison (G.obj zero)) :=
    (P.map_comp _ _).symm.trans
      ((P.congr_map (constantComparison_naturality (F.obj zero) (a.app zero)).symm).trans
        (P.map_comp _ _))
  apply (cancel_mono (P.map (constantComparison (G.obj zero)))).mp
  change (P.map (H.map a) ≫ (comparisonToZero G hG).hom) ≫
      P.map (constantComparison (G.obj zero)) =
    ((comparisonToZero F hSucc).hom ≫ P.map (a.app zero)) ≫
      P.map (constantComparison (G.obj zero))
  rw [Category.assoc, comparisonToZero_span, hl, ← comparisonToZero_span F hSucc,
    Category.assoc, hc, ← Category.assoc]

/-- The actual inverse comparison keeps the same full inverse-diagram square. -/
theorem comparisonToZero_inv_naturality {G : ℕᵒᵖ ⥤ SSet.{z}} [IsFibrant (G.obj zero)]
    (hG : ∀ n : ℕ, weakEquivalences SSet.{z} (G.map ((homOfLE (Nat.le_succ n)).op)))
    (a : F ⟶ G) :
    DerivedDiagramConstructions.scalarProjection.{z}.map (a.app zero) ≫
        (comparisonToZero G hG).inv =
      (comparisonToZero F hSucc).inv ≫
        DerivedDiagramConstructions.scalarProjection.{z}.map
          ((DerivedDiagramConstructions.scalarHomotopyLimit.{0, 0, z} ℕᵒᵖ).map a) := by
  apply (cancel_mono (comparisonToZero G hG).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, comparisonToZero_naturality F hSucc hG a, Iso.inv_hom_id_assoc]

end InverseDiagram

end HomotopicalAlgebra.ScalarInverseHomotopyLimit
