/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import MathlibExt.CategoryTheory.SmallObject.IsoEligibility
import MathlibExt.CategoryTheory.SmallObject.FullyFaithful

/-!
# Small representatives for every original free image

Only the actual representative labels are made small. Every original index
object and base arrow is retained through the original unit and an actual
Hom-coproduct comparison. The small representative family has the same
isomorphism saturation, right class and generated left class as the possibly
larger all-original family. Its eligibility uses the same base cardinal.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory Limits MorphismProperty
open HomotopicalAlgebra.FunctorProjective.IndexEquivalence

namespace HomotopicalAlgebra.FunctorProjective

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocallySmall.{w} D] [LocallySmall.{w} S]

namespace Representatives

/-- An actual original index isomorphism reindexes every Hom coproduct label. -/
def indexHomEquiv {x y : D} (e : x ≅ y) (z : D) : (x ⟶ z) ≃ (y ⟶ z) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  right_inv f := by simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The full original index comparison uses actual coproduct reindexing at each component. -/
def indexComponentIso (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) (z : D) :
    ((freeFunctor d x).obj A).obj z ≅ ((freeFunctor d y).obj A).obj z := by
  letI : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.reindex (indexHomEquiv e z) (fun _ : y ⟶ z => A)

/-- The original free insertion is typed at its unchanged free-diagram component. -/
def indexInsertion (d : CofibrantGenerationData M κ) (x : D) (A : M) (z : D) (f : x ⟶ z) :
    A ⟶ ((freeFunctor d x).obj A).obj z := by
  letI : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.ι (fun _ : x ⟶ z => A) f

/-- Every original generator insertion retains the literal inverse index map. -/
theorem indexComponentIso_insertion (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) (z : D) (f : x ⟶ z) :
    indexInsertion d x A z f ≫ (indexComponentIso d e A z).hom =
      indexInsertion d y A z (e.inv ≫ f) := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact Sigma.ι_reindex_hom (indexHomEquiv e z) (fun _ : y ⟶ z => A) f

/-- Every inverse comparison insertion retains the actual original index hom map. -/
theorem indexComponentIso_insertion_inv (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) (z : D) (f : y ⟶ z) :
    indexInsertion d y A z f ≫ (indexComponentIso d e A z).inv =
      indexInsertion d x A z (e.hom ≫ f) := by
  have h := indexComponentIso_insertion d e A z (e.hom ≫ f)
  have hIndex : e.inv ≫ (e.hom ≫ f) = f := by
    simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [hIndex] at h
  exact (Iso.comp_inv_eq (indexComponentIso d e A z)).mpr h.symm

omit [LocallySmall.{w} D] in
/-- The whole index Hom forward function is the original inverse-component composition. -/
theorem indexHomEquiv_forward_function {x y : D} (e : x ≅ y) :
    (fun (z : D) (f : x ⟶ z) => indexHomEquiv e z f) =
      fun (z : D) (f : x ⟶ z) => e.inv ≫ f := rfl

omit [LocallySmall.{w} D] in
/-- The whole inverse Hom function is the original forward-component composition. -/
theorem indexHomEquiv_inverse_function {x y : D} (e : x ≅ y) :
    (fun (z : D) (f : y ⟶ z) => (indexHomEquiv e z).symm f) =
      fun (z : D) (f : y ⟶ z) => e.hom ≫ f := rfl

/-- The whole component comparison retains every original diagram action. -/
theorem indexComponentIso_naturality (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) {z z' : D} (g : z ⟶ z') :
    ((freeFunctor d x).obj A).map g ≫ (indexComponentIso d e A z').hom =
      (indexComponentIso d e A z).hom ≫ ((freeFunctor d y).obj A).map g := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  apply Sigma.hom_ext
  intro f
  have hx : indexInsertion d x A z f ≫ ((freeFunctor d x).obj A).map g =
      indexInsertion d x A z' (f ≫ g) := by
    simp only [indexInsertion, freeFunctor, evaluationLeftAdjoint, colimit.ι_desc, Cofan.mk_ι_app]
  have hy : indexInsertion d y A z (e.inv ≫ f) ≫
      ((freeFunctor d y).obj A).map g =
      indexInsertion d y A z' ((e.inv ≫ f) ≫ g) := by
    simp only [indexInsertion, freeFunctor, evaluationLeftAdjoint, colimit.ι_desc, Cofan.mk_ι_app]
  calc
    indexInsertion d x A z f ≫
        (((freeFunctor d x).obj A).map g ≫ (indexComponentIso d e A z').hom) =
        (indexInsertion d x A z f ≫ ((freeFunctor d x).obj A).map g) ≫
          (indexComponentIso d e A z').hom := (Category.assoc _ _ _).symm
    _ = indexInsertion d x A z' (f ≫ g) ≫
        (indexComponentIso d e A z').hom := congrArg (fun h => h ≫ _) hx
    _ = indexInsertion d y A z' (e.inv ≫ (f ≫ g)) :=
      indexComponentIso_insertion d e A z' (f ≫ g)
    _ = indexInsertion d y A z' ((e.inv ≫ f) ≫ g) := by rw [Category.assoc]
    _ = indexInsertion d y A z (e.inv ≫ f) ≫ ((freeFunctor d y).obj A).map g :=
      hy.symm
    _ = (indexInsertion d x A z f ≫ (indexComponentIso d e A z).hom) ≫
        ((freeFunctor d y).obj A).map g :=
      congrArg (fun h => h ≫ _) (indexComponentIso_insertion d e A z f).symm
    _ = indexInsertion d x A z f ≫
        ((indexComponentIso d e A z).hom ≫ ((freeFunctor d y).obj A).map g) :=
      Category.assoc _ _ _

/-- The whole index comparison retains every actual coefficient map. -/
theorem indexComponentIso_coefficient (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) {A B : M} (f : A ⟶ B) (z : D) :
    ((freeFunctor d x).map f).app z ≫ (indexComponentIso d e B z).hom =
      (indexComponentIso d e A z).hom ≫ ((freeFunctor d y).map f).app z := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  apply Sigma.hom_ext
  intro h
  have hx : indexInsertion d x A z h ≫ ((freeFunctor d x).map f).app z =
      f ≫ indexInsertion d x B z h := by
    simp only [indexInsertion, freeFunctor, evaluationLeftAdjoint, colimit.ι_desc, Cofan.mk_ι_app]
  have hy : indexInsertion d y A z (e.inv ≫ h) ≫ ((freeFunctor d y).map f).app z =
      f ≫ indexInsertion d y B z (e.inv ≫ h) := by
    simp only [indexInsertion, freeFunctor, evaluationLeftAdjoint, colimit.ι_desc, Cofan.mk_ι_app]
  calc
    indexInsertion d x A z h ≫
        (((freeFunctor d x).map f).app z ≫ (indexComponentIso d e B z).hom) =
        (indexInsertion d x A z h ≫ ((freeFunctor d x).map f).app z) ≫
          (indexComponentIso d e B z).hom := (Category.assoc _ _ _).symm
    _ = (f ≫ indexInsertion d x B z h) ≫ (indexComponentIso d e B z).hom :=
      congrArg (fun k => k ≫ _) hx
    _ = f ≫ indexInsertion d y B z (e.inv ≫ h) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => f ≫ k) (indexComponentIso_insertion d e B z h))
    _ = indexInsertion d y A z (e.inv ≫ h) ≫ ((freeFunctor d y).map f).app z :=
      hy.symm
    _ = (indexInsertion d x A z h ≫ (indexComponentIso d e A z).hom) ≫
        ((freeFunctor d y).map f).app z :=
      congrArg (fun k => k ≫ _) (indexComponentIso_insertion d e A z h).symm
    _ = indexInsertion d x A z h ≫
        ((indexComponentIso d e A z).hom ≫ ((freeFunctor d y).map f).app z) :=
      Category.assoc _ _ _

/-- The actual original index isomorphism compares both complete free coefficient functors. -/
def indexFreeIso (d : CofibrantGenerationData M κ) {x y : D} (e : x ≅ y) :
    freeFunctor d x ≅ freeFunctor d y :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents (fun z => indexComponentIso d e A z)
      (fun {_ _} g => indexComponentIso_naturality d e A g))
    (fun {_ _} f => by ext z; exact indexComponentIso_coefficient d e f z)

/-- Every whole forward free component is the same actual Hom-coproduct comparison. -/
theorem indexFreeIso_hom_function (d : CofibrantGenerationData M κ) {x y : D} (e : x ≅ y) :
    (fun (A : M) (z : D) => ((indexFreeIso d e).hom.app A).app z) =
      fun (A : M) (z : D) => (indexComponentIso d e A z).hom := rfl

/-- Every whole inverse free component is the same actual Hom-coproduct inverse. -/
theorem indexFreeIso_inv_function (d : CofibrantGenerationData M κ) {x y : D} (e : x ≅ y) :
    (fun (A : M) (z : D) => ((indexFreeIso d e).inv.app A).app z) =
      fun (A : M) (z : D) => (indexComponentIso d e A z).inv := rfl

/-- The chosen source unit insertion retains the actual original identity index Hom. -/
theorem indexUnit_insertion (d : CofibrantGenerationData M κ) (x : D) (A : M) :
    (freeEvaluationAdjunction d x).unit.app A = indexInsertion d x A x (𝟙 x) := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact evaluationAdjunctionRight_unit_app M x A

/-- The chosen original counit evaluates every actual original index insertion. -/
theorem indexCounit_insertion (d : CofibrantGenerationData M κ) (x z : D)
    (X : D ⥤ M) (f : x ⟶ z) :
    indexInsertion d x (X.obj x) z f ≫ ((freeEvaluationAdjunction d x).counit.app X).app z =
      X.map f := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  simp only [indexInsertion, freeEvaluationAdjunction,
    evaluationAdjunctionRight_counit_app_app, Functor.id_obj]
  change Sigma.ι (fun _ : x ⟶ z => X.obj x) f ≫
      Sigma.desc (f := fun _ : x ⟶ z => X.obj x) (fun f : x ⟶ z => X.map f) = X.map f
  exact Sigma.ι_comp_desc (f := fun _ : x ⟶ z => X.obj x) (fun f : x ⟶ z => X.map f) f

/-- The whole unit function preserves all actual original object and coefficient domains. -/
theorem indexUnit_insertion_function (d : CofibrantGenerationData M κ) :
    (fun (x : D) (A : M) => (freeEvaluationAdjunction d x).unit.app A) =
      fun (x : D) (A : M) => indexInsertion d x A x (𝟙 x) := by
  funext x A
  exact indexUnit_insertion d x A

/-- The original source unit follows the original inverse index insertion under comparison. -/
theorem indexFreeIso_unit (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) :
    (freeEvaluationAdjunction d x).unit.app A ≫ ((indexFreeIso d e).hom.app A).app x =
      indexInsertion d y A x e.inv := by
  calc
    (freeEvaluationAdjunction d x).unit.app A ≫ ((indexFreeIso d e).hom.app A).app x =
        indexInsertion d x A x (𝟙 x) ≫ (indexComponentIso d e A x).hom :=
      congrArg₂ (fun f g => f ≫ g) (indexUnit_insertion d x A)
        (congrFun (congrFun (indexFreeIso_hom_function d e) A) x)
    _ = indexInsertion d y A x (e.inv ≫ 𝟙 x) := indexComponentIso_insertion d e A x _
    _ = indexInsertion d y A x e.inv := congrArg (indexInsertion d y A x) (Category.comp_id _)

/-- The original target unit follows the actual forward index insertion under the inverse. -/
theorem indexFreeIso_unit_inv (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) (A : M) :
    (freeEvaluationAdjunction d y).unit.app A ≫ ((indexFreeIso d e).inv.app A).app y =
      indexInsertion d x A y e.hom := by
  calc
    (freeEvaluationAdjunction d y).unit.app A ≫ ((indexFreeIso d e).inv.app A).app y =
        indexInsertion d y A y (𝟙 y) ≫ (indexComponentIso d e A y).inv :=
      congrArg₂ (fun f g => f ≫ g) (indexUnit_insertion d y A)
        (congrFun (congrFun (indexFreeIso_inv_function d e) A) y)
    _ = indexInsertion d x A y (e.hom ≫ 𝟙 y) := indexComponentIso_insertion_inv d e A y _
    _ = indexInsertion d x A y e.hom := congrArg (indexInsertion d x A y) (Category.comp_id _)

/-- The complete original counit function retains every source-index insertion and action. -/
theorem indexCounit_insertion_function (d : CofibrantGenerationData M κ) :
    (fun (x z : D) (X : D ⥤ M) (f : x ⟶ z) =>
      indexInsertion d x (X.obj x) z f ≫ ((freeEvaluationAdjunction d x).counit.app X).app z) =
      fun (x z : D) (X : D ⥤ M) (f : x ⟶ z) => X.map f := by
  funext x z X f
  exact indexCounit_insertion d x z X f

/-- The whole original forward free comparison is natural in every coefficient arrow. -/
theorem indexFreeIso_coefficient_function (d : CofibrantGenerationData M κ) {x y : D}
    (e : x ≅ y) :
    (fun (A B : M) (f : A ⟶ B) (z : D) =>
      ((freeFunctor d x).map f).app z ≫ ((indexFreeIso d e).hom.app B).app z) =
      fun (A B : M) (f : A ⟶ B) (z : D) =>
        ((indexFreeIso d e).hom.app A).app z ≫ ((freeFunctor d y).map f).app z := by
  funext A B f z
  exact indexComponentIso_coefficient d e f z

omit [LocallySmall.{w} D]

/-- Every original free-image arrow retains both actual original index comparison components. -/
def originalFreeArrowIso (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (x : D) (f : Arrow M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    Arrow.mk ((freeFunctor d x).map f.hom) ≅
      Arrow.mk ((freeFunctor d (e.inverse.obj (e.functor.obj x))).map f.hom) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact ((Functor.mapArrowFunctor M (D ⥤ M)).mapIso (indexFreeIso d (e.unitIso.app x))).app f

/-- The whole original free-image comparison retains all four endpoint component functions. -/
theorem originalFreeArrowIso_fields (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (x : D) (f : Arrow M) (z : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (originalFreeArrowIso e d x f).hom.left.app z =
        (indexComponentIso d (e.unitIso.app x) f.left z).hom ∧
      (originalFreeArrowIso e d x f).hom.right.app z =
        (indexComponentIso d (e.unitIso.app x) f.right z).hom ∧
      (originalFreeArrowIso e d x f).inv.left.app z =
        (indexComponentIso d (e.unitIso.app x) f.left z).inv ∧
      (originalFreeArrowIso e d x f).inv.right.app z =
        (indexComponentIso d (e.unitIso.app x) f.right z).inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual representative family keeps the original inverse-object and base-arrow labels. -/
def family (e : D ≌ S) (d : CofibrantGenerationData M κ) (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    MorphismProperty (D ⥤ M) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact adjointFamilyGenerators (fun s : S => freeFunctor d (e.inverse.obj s)) P

/-- Representative membership is equality of the entire original free-image arrow. -/
theorem family_iff (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) {X Y : D ⥤ M} (f : X ⟶ Y) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P f ↔ ∃ q : S × P.toSet,
      Arrow.mk f = Arrow.mk ((freeFunctor d (e.inverse.obj q.1)).map q.2.1.hom) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact adjointFamilyGenerators_iff
    (fun s : S => freeFunctor (D := D) d (e.inverse.obj s)) P f

/-- Every representative is literally an original free image, without isomorphism closure. -/
theorem family_le_allOriginal (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P ≤ freeGenerators d P := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rintro X Y f ⟨q⟩
  exact freeGenerator_mem d P (e.inverse.obj q.1) q.2.1.hom q.2.2

/-- Every original object and base arrow belongs to the representative isomorphism saturation. -/
theorem allOriginal_le_family_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    freeGenerators d P ≤ (family e d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rintro X Y f ⟨q⟩
  refine ⟨_, _, (freeFunctor d (e.inverse.obj (e.functor.obj q.1))).map q.2.1.hom, ?_, ?_⟩
  · exact map_mem_adjointFamilyGenerators
      (fun s : S => freeFunctor (D := D) d (e.inverse.obj s)) P
      (e.functor.obj q.1) q.2.1.hom q.2.2
  · exact ⟨(originalFreeArrowIso e d q.1 q.2.1).symm⟩

/-- The complete original family and actual representatives have equal isomorphism saturation. -/
theorem family_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).isoClosure = (freeGenerators d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  apply le_antisymm
  · exact monotone_isoClosure (family_le_allOriginal e d P)
  · exact (isoClosure_le_iff _ _).mpr (allOriginal_le_family_isoClosure e d P)

/-- Only the genuine representative label carrier is used to prove actual family smallness. -/
theorem family_isSmall (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] [P.IsSmall.{w}] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).IsSmall.{w} := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact adjointFamilyGenerators_isSmall
    (fun s : S => freeFunctor (D := D) d (e.inverse.obj s)) P

/-- Every representative right-lifting test is the original actual evaluation adjunction. -/
theorem family_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp = P.rlp.functorCategory D := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  ext X Y f
  refine (adjointFamilyGenerators_rlp_iff
    (fun s : S => freeFunctor d (e.inverse.obj s))
    (fun s : S => (evaluation D M).obj (e.inverse.obj s))
    (fun s : S => freeEvaluationAdjunction d (e.inverse.obj s)) P f).trans ?_
  change (∀ s : S, P.rlp (f.app (e.inverse.obj s))) ↔ ∀ x : D, P.rlp (f.app x)
  constructor
  · intro hf x
    exact (P.rlp.arrow_mk_iso_iff (unitComponentArrowIso e f x)).mpr (hf (e.functor.obj x))
  · intro hf s
    exact hf (e.inverse.obj s)

/-- Both complete right classes coincide on every original natural transformation. -/
theorem family_rlp_eq_allOriginal (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp = (freeGenerators d P).rlp := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [family_rlp, freeGenerators_rlp]

/-- Both complete generated left classes coincide on every original natural transformation. -/
theorem family_left_eq_allOriginal (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp.llp = (freeGenerators d P).rlp.llp := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact congrArg MorphismProperty.llp (family_rlp_eq_allOriginal e d P)

/-- Every strict mapped representative is isomorphic to an actual small-side free image. -/
theorem mapped_family_le_small_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).strictMap (e.congrLeft (E := M)).functor ≤
      (freeGenerators (D := S) d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rintro X Y f ⟨hf⟩
  obtain ⟨q⟩ := hf
  refine ⟨_, _, (freeFunctor (D := S) d q.1).map q.2.1.hom, ?_, ?_⟩
  · exact freeGenerator_mem d P q.1 q.2.1.hom q.2.2
  · exact ⟨((freeArrowComparison e d q.1).app q.2.1).symm⟩

/-- The normalized small target retains all original target and strict mapped representatives. -/
def normalizedTarget (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    MorphismProperty (S ⥤ M) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeGenerators (D := S) d P ⊔ (family e d P).strictMap (e.congrLeft (E := M)).functor

/-- Actual binary smallness is proved from the two genuine small label carriers. -/
theorem normalizedTarget_isSmall (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] [P.IsSmall.{w}] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (normalizedTarget e d P).IsSmall.{w} := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : (freeGenerators (D := S) d P).IsSmall.{w} :=
    adjointFamilyGenerators_isSmall _ P
  let _ : (family e d P).IsSmall.{w} := family_isSmall e d P
  let _ : ((family e d P).strictMap (e.congrLeft (E := M)).functor).IsSmall.{w} :=
    IsSmall.strictMap (family_isSmall e d P) _
  rw [normalizedTarget, sup_eq_iSup]
  let _ (b : Bool) : (cond b (freeGenerators (D := S) d P)
      ((family e d P).strictMap (e.congrLeft (E := M)).functor)).IsSmall.{w} := by
    cases b
    · exact inferInstanceAs
        (((family e d P).strictMap (e.congrLeft (E := M)).functor).IsSmall.{w})
    · exact inferInstanceAs ((freeGenerators (D := S) d P).IsSmall.{w})
  infer_instance

/-- Normalization preserves the genuine small-side isomorphism saturation. -/
theorem normalizedTarget_le_isoClosure (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    normalizedTarget e d P ≤ (freeGenerators (D := S) d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact sup_le (le_isoClosure _) (mapped_family_le_small_isoClosure e d P)

/-- The actual normalized target supplies the literal inclusion required for SOA transfer. -/
theorem family_le_normalized_inverseImage (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P ≤ (normalizedTarget e d P).inverseImage (e.congrLeft (E := M)).functor := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact fun _ _ f hf => Or.inr (map_mem_strictMap _ _ f hf)

omit [LocallySmall.{w} D] [LocallySmall.{w} S] in
/-- The actual original diagram category has working-size Homs through the same faithful map. -/
theorem originalFunctor_locallySmall (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] : LocallySmall.{w} (D ⥤ M) := by
  let _ : LocallySmall.{w} M := d.I_smallObject.locallySmall
  let _ : LocallySmall.{w} (S ⥤ M) :=
    { hom_small F G := small_of_injective (f := fun η : F ⟶ G => fun s : S => η.app s)
        (fun _ _ h => NatTrans.ext h) }
  exact locallySmall_of_faithful (e.congrLeft (E := M)).functor

/-- The normalized target is eligible at the exact original base cardinal. -/
theorem normalizedTarget_eligible (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (normalizedTarget e d P).IsCardinalForSmallObjectArgument κ := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : P.IsSmall.{w} := hP.isSmall
  let _ : (freeGenerators (D := S) d P).IsCardinalForSmallObjectArgument κ :=
    freeGenerators_eligible d P hP
  let _ : (normalizedTarget e d P).IsSmall.{w} := normalizedTarget_isSmall e d P
  let _ : LocallySmall.{w} M := hP.locallySmall
  let _ : LocallySmall.{w} (S ⥤ M) := SmallObject.locallySmall (freeGenerators (D := S) d P) κ
  let _ : HasPushouts M := hP.hasPushouts
  let _ : HasCoproducts.{w} M := hP.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType M := hP.hasIterationOfShape
  exact isCardinalForSmallObjectArgument_of_isoClosure
    (normalizedTarget e d P) (freeGenerators (D := S) d P) κ
    (normalizedTarget_le_isoClosure e d P)

/-- Every representative has all six actual fields at the same original cardinal and bottom. -/
theorem family_eligible (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).IsCardinalForSmallObjectArgument κ := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  let _ : P.IsSmall.{w} := hP.isSmall
  let _ : (family e d P).IsSmall.{w} := family_isSmall e d P
  let _ : LocallySmall.{w} (D ⥤ M) := originalFunctor_locallySmall e d
  let _ : HasPushouts M := hP.hasPushouts
  let _ : HasCoproducts.{w} M := hP.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType M := hP.hasIterationOfShape
  let _ : (normalizedTarget e d P).IsCardinalForSmallObjectArgument κ :=
    normalizedTarget_eligible e d P hP
  exact IsCardinalForSmallObjectArgument.of_fullyFaithful
    (e.congrLeft (E := M)).functor (family e d P) (normalizedTarget e d P) κ
    (family_le_normalized_inverseImage e d P)

/-- The original base I produces the actual small representative I-family at the same κ. -/
theorem familyI_eligible (e : D ≌ S) (d : CofibrantGenerationData M κ) [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d d.I).IsCardinalForSmallObjectArgument κ := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_eligible e d d.I d.I_smallObject

/-- The original base J produces the actual small representative J-family at the same κ. -/
theorem familyJ_eligible (e : D ≌ S) (d : CofibrantGenerationData M κ) [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d d.J).IsCardinalForSmallObjectArgument κ := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_eligible e d d.J d.J_smallObject

/-- The same actual original representative family has its original chosen SOA factor value. -/
def factorizationData (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    FunctorialFactorizationData (family e d P).rlp.llp (family e d P).rlp := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
  exact SmallObject.functorialFactorizationData (family e d P) κ

/-- The full chosen factorization record is the existing SOA algorithm at the same κ. -/
theorem factorizationData_eq (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    factorizationData e d P hP = SmallObject.functorialFactorizationData (family e d P) κ := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire middle functor remains the original representative-family SOA functor. -/
theorem factorizationData_Z (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationData e d P hP).Z =
      (SmallObject.functorialFactorizationData (family e d P) κ).Z := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire left factor retains the original representative-family cellular inclusion. -/
theorem factorizationData_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationData e d P hP).i =
      (SmallObject.functorialFactorizationData (family e d P) κ).i := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire right factor retains the original representative-family SOA projection. -/
theorem factorizationData_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationData e d P hP).p =
      (SmallObject.functorialFactorizationData (family e d P) κ).p := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The actual representative SOA factorization retains every original diagram component. -/
theorem factorizationData_fac_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    (f : Arrow (D ⥤ M)) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((factorizationData e d P hP).i.app f).app x ≫
      ((factorizationData e d P hP).p.app f).app x = f.hom.app x := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  have h : (factorizationData e d P hP).i.app f ≫
      (factorizationData e d P hP).p.app f = f.hom :=
    (factorizationData e d P hP).fac_app
  exact congrArg (fun a : f.left ⟶ f.right => a.app x) h

/-- The actual middle map keeps every original Arrow identity. -/
theorem factorizationData_map_id (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    (f : Arrow (D ⥤ M)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (factorizationData e d P hP).Z.map (𝟙 f) = 𝟙 ((factorizationData e d P hP).Z.obj f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d P hP).Z.map_id f

/-- The actual middle map keeps every original Arrow composition. -/
theorem factorizationData_map_comp (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    {f g k : Arrow (D ⥤ M)} (a : f ⟶ g) (b : g ⟶ k) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (factorizationData e d P hP).Z.map (a ≫ b) =
      (factorizationData e d P hP).Z.map a ≫ (factorizationData e d P hP).Z.map b := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d P hP).Z.map_comp a b

/-- The actual left factor retains every original Arrow-square naturality equation. -/
theorem factorizationData_i_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    a.left ≫ (factorizationData e d P hP).i.app g =
      (factorizationData e d P hP).i.app f ≫ (factorizationData e d P hP).Z.map a := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d P hP).i.naturality a

/-- The actual right factor retains every original Arrow-square naturality equation. -/
theorem factorizationData_p_naturality (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (factorizationData e d P hP).Z.map a ≫ (factorizationData e d P hP).p.app g =
      (factorizationData e d P hP).p.app f ≫ a.right := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d P hP).p.naturality a

/-- The actual left naturality retains every original diagram component. -/
theorem factorizationData_i_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    a.left.app x ≫ ((factorizationData e d P hP).i.app g).app x =
      ((factorizationData e d P hP).i.app f).app x ≫
        ((factorizationData e d P hP).Z.map a).app x := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact congrArg (fun h : f.left ⟶ (factorizationData e d P hP).Z.obj g => h.app x)
    (factorizationData_i_naturality e d P hP a)

/-- The actual right naturality retains every original diagram component. -/
theorem factorizationData_p_naturality_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    {f g : Arrow (D ⥤ M)} (a : f ⟶ g) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((factorizationData e d P hP).Z.map a).app x ≫
        ((factorizationData e d P hP).p.app g).app x =
      ((factorizationData e d P hP).p.app f).app x ≫ a.right.app x := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact congrArg (fun h : (factorizationData e d P hP).Z.obj f ⟶ g.right => h.app x)
    (factorizationData_p_naturality e d P hP a)

/-- The returned original SOA factor keeps its actual relative-cell witness. -/
def factorizationCellComplex (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    (f : Arrow (D ⥤ M)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => (family e d P).homFamily)
      ((factorizationData e d P hP).i.app f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
  exact SmallObject.relativeCellComplexιObj (family e d P) κ f.hom

/-- The entire chosen relative-cell chain is the original SOA iteration functor. -/
theorem factorizationCellComplex_F (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    (f : Arrow (D ⥤ M)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationCellComplex e d P hP f).F =
      (SmallObject.relativeCellComplexιObj (family e d P) κ f.hom).F := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire chosen relative-cell inclusion is the original SOA inclusion family. -/
theorem factorizationCellComplex_incl (e : D ≌ S) (d : CofibrantGenerationData M κ)
    (P : MorphismProperty M) [Small.{w} S] (hP : P.IsCardinalForSmallObjectArgument κ)
    (f : Arrow (D ⥤ M)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationCellComplex e d P hP f).incl =
      (SmallObject.relativeCellComplexιObj (family e d P) κ f.hom).incl := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The original representative I factorization uses the exact existing fixed-cardinal record. -/
def cofibrantFactorizationData (e : D ≌ S) (d : CofibrantGenerationData M κ) [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    FunctorialFactorizationData (family e d d.I).rlp.llp
      ((trivialFibrations M).functorCategory D) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d d.I d.I_smallObject).ofLE le_rfl
    (by rw [family_rlp, d.I_rlp])

/-- The original representative J factorization uses that same input cardinal and base datum. -/
def fibrantFactorizationData (e : D ≌ S) (d : CofibrantGenerationData M κ) [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    FunctorialFactorizationData (family e d d.J).rlp.llp
      ((fibrations M).functorCategory D) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact (factorizationData e d d.J d.J_smallObject).ofLE le_rfl
    (by rw [family_rlp, d.J_rlp])

/-- The entire I intermediate functor is unchanged by the membership conversion. -/
theorem cofibrantFactorizationData_Z (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (cofibrantFactorizationData e d).Z = (factorizationData e d d.I d.I_smallObject).Z := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The entire J intermediate functor is unchanged by the membership conversion. -/
theorem fibrantFactorizationData_Z (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fibrantFactorizationData e d).Z = (factorizationData e d d.J d.J_smallObject).Z := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The complete I left factor keeps the original chosen representative-family inclusion. -/
theorem cofibrantFactorizationData_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (cofibrantFactorizationData e d).i = (factorizationData e d d.I d.I_smallObject).i := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The complete I right factor keeps the original chosen representative-family projection. -/
theorem cofibrantFactorizationData_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (cofibrantFactorizationData e d).p = (factorizationData e d d.I d.I_smallObject).p := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The complete J left factor keeps the original chosen representative-family inclusion. -/
theorem fibrantFactorizationData_i (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fibrantFactorizationData e d).i = (factorizationData e d d.J d.J_smallObject).i := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The complete J right factor keeps the original chosen representative-family projection. -/
theorem fibrantFactorizationData_p (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fibrantFactorizationData e d).p = (factorizationData e d d.J d.J_smallObject).p := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact rfl

/-- The actual I-factorization satisfies the exact factor equation at every original component. -/
theorem cofibrantFactorizationData_fac_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] (f : Arrow (D ⥤ M)) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((cofibrantFactorizationData e d).i.app f).app x ≫
      ((cofibrantFactorizationData e d).p.app f).app x = f.hom.app x := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact factorizationData_fac_app e d d.I d.I_smallObject f x

/-- The actual J-factorization satisfies the exact factor equation at every original component. -/
theorem fibrantFactorizationData_fac_app (e : D ≌ S) (d : CofibrantGenerationData M κ)
    [Small.{w} S] (f : Arrow (D ⥤ M)) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((fibrantFactorizationData e d).i.app f).app x ≫
      ((fibrantFactorizationData e d).p.app f).app x = f.hom.app x := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact factorizationData_fac_app e d d.J d.J_smallObject f x

/-- Both representative right classes retain all original objectwise base right equations. -/
theorem familyI_familyJ_rlp (e : D ≌ S) (d : CofibrantGenerationData M κ) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d d.I).rlp = (trivialFibrations M).functorCategory D ∧
      (family e d d.J).rlp = (fibrations M).functorCategory D := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [family_rlp, family_rlp, d.I_rlp, d.J_rlp]
  exact ⟨rfl, rfl⟩

end Representatives

end HomotopicalAlgebra.FunctorProjective
