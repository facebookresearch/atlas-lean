/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebraConstruction
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorInterfaces
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorColimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Colimits of tensor-operadic algebras

Under the specified finite-tensor colimit-preservation and profile-colimit
hypotheses, the algebra forgetful functor creates filtered colimits and
reflexive coequalizers. The construction equips the carrier colimits
with operations compatible with the profile tensors and algebra maps.
-/

section source_ProfileCarrierFunctor
/-!
## Original coefficient-weighted profile tensor functors on carrier families
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original fixed profile tensor is functorial in every
original color-indexed carrier component map. -/
def profileCarrierSummandFunctor (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) : (W → C) ⥤ C where
  obj A := (analyticSummand O A).obj P
  map f := (analyticSummandCarrierMap O f).app P
  map_id A := congrArg (fun a => a.app P) (analyticSummandCarrierMap_id O (A := A))
  map_comp f g := congrArg (fun a => a.app P) (analyticSummandCarrierMap_comp O f g)

/-- Retain the original coefficient and evaluate every original
carrier input color in its actual finite profile slot. -/
def profileCarrierFactorsFunctor (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) : (W → C) ⥤ (analyticFactorsIndex P → C) where
  obj A i := match i with
    | none => O.obj P.toColoredProfile
    | some i => A (P.inputColor i)
  map f i := match i with
    | none => 𝟙 (O.obj P.toColoredProfile)
    | some i => f (P.inputColor i)
  map_id A := by
    funext i
    cases i <;> rfl
  map_comp f g := by
    funext i
    cases i with
    | none => exact (Category.id_comp _).symm
    | some i => rfl

/-- The original finite coefficient/input factors identify with
the fixed-slot carrier factors by identity component isomorphisms. -/
def profileCarrierFactorsIso (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) (A : W → C) :
    (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex P)).obj
      ((profileCarrierFactorsFunctor O P).obj A) ≅
      (analyticFactors O A).obj P :=
  FiniteFamily.isoOfComponents (Equiv.refl (Option P.inputs))
    (fun i => match i with
      | none => Iso.refl (O.obj P.toColoredProfile)
      | some i => Iso.refl (A (P.inputColor i)))

omit [FiniteTensor C] in
/-- The actual original carrier factor maps commute with the
actual original finite factor isomorphisms in every color slot. -/
theorem profileCarrierFactorsIso_naturality (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) {A B : W → C} (f : A ⟶ B) :
    (FiniteFamily.fixedIndexFunctor (analyticFactorsIndex P)).map
      ((profileCarrierFactorsFunctor O P).map f) ≫
      (profileCarrierFactorsIso O P B).hom =
    (profileCarrierFactorsIso O P A).hom ≫ (analyticFactorsCarrierMap O f).app P := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none => exact HEq.rfl
    | some i => exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Tensoring the original carrier factors gives an actual
isomorphism with the original profile tensor summand object. -/
def profileCarrierTensorObjIso (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) (A : W → C) :
    (profileCarrierFactorsFunctor O P ⋙ fixedIndexTensorFunctor (C :=
      C) (analyticFactorsIndex P)).obj A ≅
      (profileCarrierSummandFunctor O P).obj A :=
  (FiniteTensor.tensor (V := C)).mapIso (profileCarrierFactorsIso O P A)

/-- The actual original component tensor map agrees with the
original profile summand carrier natural-transformation component. -/
theorem profileCarrierTensor_map (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) {A B : W → C} (f : A ⟶ B) :
    (profileCarrierFactorsFunctor O P ⋙ fixedIndexTensorFunctor (C :=
      C) (analyticFactorsIndex P)).map f ≫
      (profileCarrierTensorObjIso O P B).hom =
    (profileCarrierTensorObjIso O P A).hom ≫ (profileCarrierSummandFunctor O P).map f := by
  change (FiniteTensor.tensor (V := C)).map _ ≫ (FiniteTensor.tensor (V := C)).map _ =
    (FiniteTensor.tensor (V := C)).map _ ≫ (analyticSummandCarrierMap O f).app P
  rw [analyticSummandCarrierMap_app]
  exact ((FiniteTensor.tensor (V := C)).map_comp _ _).symm.trans
    ((congrArg (FiniteTensor.tensor (V := C)).map (profileCarrierFactorsIso_naturality O P f)).trans
      ((FiniteTensor.tensor (V := C)).map_comp _ _))

/-- The decomposition into original coefficient and carrier slot
evaluation functors is a full natural isomorphism of tensor functors. -/
def profileCarrierTensorIso (O : ColoredSymmetricCollection W C) {d : W} (P : AnalyticIndex W d) :
    profileCarrierFactorsFunctor O P ⋙ fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P) ≅
      profileCarrierSummandFunctor O P :=
  NatIso.ofComponents (profileCarrierTensorObjIso O P) (by
    intro A B f
    exact profileCarrierTensor_map O P f)


end CategoryTheory.Operad.Tensor
end
end
end source_ProfileCarrierFunctor


section source_ProfileDiagramCarrierFunctor
/-!
## Original profile-diagram carrier functor and coinvariant component
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]

/-- The original carrier family determines its complete original
fixed-output profile diagram, with all actual profile permutations. -/
def profileDiagramCarrierFunctor (O : ColoredSymmetricCollection W C) (d : W) :
    (W → C) ⥤ (AnalyticIndex W d ⥤ C) where
  obj A := analyticSummand O A
  map f := analyticSummandCarrierMap O f
  map_id _ := analyticSummandCarrierMap_id O
  map_comp f g := analyticSummandCarrierMap_comp O f g

/-- Evaluating at an original profile is the original complete
coefficient-weighted profile tensor carrier functor. -/
def profileDiagramEvaluationIso (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) :
    profileDiagramCarrierFunctor O d ⋙ (evaluation (AnalyticIndex W d) C).obj P ≅
      profileCarrierSummandFunctor O P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The original output component of profile coinvariants is the
actual profile-diagram carrier functor followed by its actual colimit. -/
def profileCoinvariantCarrierFunctor (O : ColoredSymmetricCollection W C) (d : W) :
    (W → C) ⥤ C := profileDiagramCarrierFunctor O d ⋙ colim

/-- The actual full colored profile functor's output component is
the actual colimit of its original complete profile diagram. -/
def profileEndofunctorEvaluationIso (O : ColoredSymmetricCollection W C) (d : W) :
    profileCoinvariantCarrierFunctor O d ≅
      profileEndofunctor O ⋙ Pi.eval (fun _ : W => C) d :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)


end CategoryTheory.Operad.Tensor
end
end
end source_ProfileDiagramCarrierFunctor


section source_ProfileCarrierSlots
/-!
## Original coefficient and color evaluation functors in each profile slot
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w uJ vJ

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C]

/-- The original coefficient slot is its constant coefficient
functor; every original input slot is its actual color evaluation. -/
def profileCarrierSlotFunctor (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) : (i : analyticFactorsIndex P) → (W → C) ⥤ C
  | none => (Functor.const (W → C)).obj (O.obj P.toColoredProfile)
  | some i => Pi.eval (fun _ : W => C) (P.inputColor i)

/-- The original slot functor is the corresponding actual
coordinate evaluation of the original carrier factor functor. -/
def profileCarrierSlotIso (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) (i : analyticFactorsIndex P) :
    profileCarrierFactorsFunctor O P ⋙ Pi.eval (fun _ : analyticFactorsIndex P => C) i ≅
      profileCarrierSlotFunctor O P i := by
  cases i with
  | none =>
    exact NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro A B f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  | some i =>
    exact NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro A B f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable {J : Type uJ} [Category.{vJ} J] [IsConnected J] [HasColimitsOfShape J C]

/-- Each original coefficient/input slot preserves connected
colimits, constructed from the coefficient constant cocone and
original color-evaluation colimits. -/
instance profileCarrierSlotPreservesColimits (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) (i : analyticFactorsIndex P) :
    PreservesColimitsOfShape J (profileCarrierSlotFunctor O P i) := by
  cases i with
  | none => exact constantPreservesConnectedColimits _
  | some i => exact piEvalPreservesColimitsOfShape _

/-- The actual original coefficient/input coordinate functors
preserve connected colimits through their proved slot isomorphisms. -/
instance profileCarrierCoordinatePreservesColimits (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) (i : analyticFactorsIndex P) :
    PreservesColimitsOfShape J (profileCarrierFactorsFunctor O P ⋙ Pi.eval (fun _ :
      analyticFactorsIndex P => C) i) :=
  preservesColimitsOfShape_of_natIso (profileCarrierSlotIso O P i).symm


end CategoryTheory.Operad.Tensor
end
end
end source_ProfileCarrierSlots


section source_ProfileSiftedSummandColimits
/-!
## Actual coefficient-weighted profile tensor commutation with sifted colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w uJ vJ us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits CategoryTheory.Limits.FiniteMultifunctor

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable {J : Type uJ} [Category.{vJ} J] [IsSifted J] [EssentiallySmall.{us} J]
variable [HasColimitsOfShape J C] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The source separate tensor preservation and actual finite
sifted diagonal construct a colimit on each original coefficient
and carrier profile tensor, including the original nullary profile. -/
def isColimitProfileCarrierTensor (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) {D : J ⥤ (W → C)} {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((profileCarrierFactorsFunctor O P ⋙
      fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)).mapCocone c) := by
  letI : DecidableEq (analyticFactorsIndex P).obj := Classical.decEq _
  letI : DecidableEq (Option P.inputs) := Classical.decEq _
  let G := profileCarrierFactorsFunctor O P
  let F := fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)
  let K := fun i : (analyticFactorsIndex P).obj => D ⋙ G ⋙ Pi.eval (fun _ :
    analyticFactorsIndex P => C) i
  let c' := fun i : (analyticFactorsIndex P).obj =>
    (G ⋙ Pi.eval (fun _ : analyticFactorsIndex P => C) i).mapCocone c
  have hc' : ∀ i : (analyticFactorsIndex P).obj, IsColimit (c' i) := fun i =>
    isColimitOfPreserves (G ⋙ Pi.eval (fun _ : analyticFactorsIndex P => C) i) hc
  letI : Functor.PreservesColimitsInEachSlot.{0, w, v, w, v, us} F :=
    FiniteTensorPreservesColimitsInEachSlot.preserves (C := C) (analyticFactorsIndex P)
  let E : finiteSiftedDiagram F K ≅ D ⋙ (G ⋙ F) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro j k f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let target := (G ⋙ F).mapCocone c
  have ht := isColimitFiniteSiftedCocone F hc'
  have hpre : IsColimit ((Cocone.precompose E.hom).obj target) := by
    apply IsColimit.ofIsoColimit ht
    refine Cocone.ext (Iso.refl _) fun j => ?_
    change F.map (G.map (c.ι.app j)) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (G.map (c.ι.app j))
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact (IsColimit.precomposeHomEquiv E target).toFun hpre

/-- The actual original coefficient/input tensor functor preserves
sifted colimits by the constructed original colimit cocone. -/
instance profileCarrierTensorPreservesColimits (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) :
    PreservesColimitsOfShape J (profileCarrierFactorsFunctor O P ⋙
      fixedIndexTensorFunctor (C := C) (analyticFactorsIndex P)) where
  preservesColimit := ⟨fun hc => ⟨isColimitProfileCarrierTensor O P hc⟩⟩

/-- The original weighted profile summand functor preserves
sifted colimits through its proved full original tensor-factor iso. -/
instance profileCarrierSummandPreservesColimits (O : ColoredSymmetricCollection W C) {d : W}
    (P : AnalyticIndex W d) : PreservesColimitsOfShape J (profileCarrierSummandFunctor O P) :=
  preservesColimitsOfShape_of_natIso (profileCarrierTensorIso O P)


end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSiftedSummandColimits


section source_ProfileSiftedPreservation
/-!
## Actual original colored tensor-profile functor preserves sifted colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w uJ vJ us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable {J : Type uJ} [Category.{vJ} J] [IsSifted J] [EssentiallySmall.{us} J]
variable [HasColimitsOfShape J C] [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

/-- The complete original fixed-output profile diagram preserves
sifted colimits because each original weighted profile tensor does.
The actual profile evaluation colimits jointly reflect the result. -/
instance profileDiagramCarrierPreservesSiftedColimits (O : ColoredSymmetricCollection W C) (d : W) :
    PreservesColimitsOfShape J (profileDiagramCarrierFunctor O d) :=
  preservesColimitsOfShape_of_evaluation _ J (fun P =>
    preservesColimitsOfShape_of_natIso (profileDiagramEvaluationIso O P).symm)

variable [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]

/-- The actual profile-coinvariant component preserves sifted
colimits. The original profile colimit is a constructed left adjoint,
so it commutes with the original already proved diagram colimits. -/
instance profileCoinvariantCarrierPreservesSiftedColimits (O : ColoredSymmetricCollection W
  C) (d : W) :
    PreservesColimitsOfShape J (profileCoinvariantCarrierFunctor O d) := by
  let : PreservesColimitsOfSize.{vJ, uJ} (colim (J := AnalyticIndex W d) (C := C)) :=
    colimConstAdj.leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesColimitsOfShape J (profileDiagramCarrierFunctor O d ⋙ colim))

/-- Every original color component of the actual profile
endofunctor preserves the original sifted colimits. -/
instance profileEndofunctorCoordinatePreservesSiftedColimits (O : ColoredSymmetricCollection
  W C) (d : W) :
    PreservesColimitsOfShape J (profileEndofunctor O ⋙ Pi.eval (fun _ : W => C) d) :=
  preservesColimitsOfShape_of_natIso (profileEndofunctorEvaluationIso O d)

/-- The actual original colored tensor-profile endofunctor
preserves sifted colimits, derived from source separate finite tensor
preservation and original profile-groupoid colimits. -/
instance profileEndofunctorPreservesSiftedColimits (O : ColoredSymmetricCollection W C) :
    PreservesColimitsOfShape J (profileEndofunctor O) :=
  preservesColimitsOfShape_of_piEvaluation _ (fun _ => inferInstance)


end CategoryTheory.Operad.Tensor
end
end
end source_ProfileSiftedPreservation


section source_TensorAlgebraSiftedLift
/-!
## Actual lifted sifted colimits of original tensor algebras

The action on the given carrier colimit is a constructed colimit
descent. Its unit and substitution equations follow from the original
diagram equations and the proved finite tensor commutation theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us uJ vJ

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem colimitUnitFromInjection {V : Type*} [Category* V]
    {A B TA TB : V} (i : A ⟶ B) (ua : A ⟶ TA) (ub : B ⟶ TB)
    (ti : TA ⟶ TB) (a : TA ⟶ A) (b : TB ⟶ B)
    (hn : i ≫ ub = ua ≫ ti) (hf : ti ≫ b = a ≫ i) (hu : ua ≫ a = 𝟙 A) :
    i ≫ (ub ≫ b) = i ≫ 𝟙 B := by
  rw [← Category.assoc i ub, hn, Category.assoc ua ti, hf,
    ← Category.assoc ua a, hu, Category.id_comp, Category.comp_id]

private theorem colimitAssocFromInjection {V : Type*} [Category* V]
    {A B TA TB TTA TTB : V} (i : A ⟶ B) (ti : TA ⟶ TB) (tti : TTA ⟶ TTB)
    (a : TA ⟶ A) (b : TB ⟶ B) (ma : TTA ⟶ TA) (mb : TTB ⟶ TB)
    (ta : TTA ⟶ TA) (tb : TTB ⟶ TB)
    (hn : tti ≫ mb = ma ≫ ti) (hf : ti ≫ b = a ≫ i)
    (hm : tti ≫ tb = ta ≫ ti) (ha : ma ≫ a = ta ≫ a) :
    tti ≫ (mb ≫ b) = tti ≫ (tb ≫ b) := by
  rw [← Category.assoc tti mb, hn, Category.assoc ma ti, hf,
    ← Category.assoc ma a, ha, Category.assoc ta a, ← hf,
    ← Category.assoc ta ti, ← hm, Category.assoc]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]
variable {J : Type uJ} [Category.{vJ} J] [IsSifted J] [EssentiallySmall.{us} J]
variable [HasColimitsOfShape J C]

/-- Every original algebra action gives the actual natural
transformation on the original carrier diagram. -/
def tensorAlgebraDiagramActions (O : ColoredOperadObj W C) (D : J ⥤ Algebra O) :
    (D ⋙ Algebra.forget O) ⋙ profileEndofunctor O.toCollection ⟶ D ⋙ Algebra.forget O where
  app j := (D.obj j).action
  naturality _ _ f := (Algebra.action_naturality (D.map f)).symm

variable {O : ColoredOperadObj W C} {D : J ⥤ Algebra O}

/-- The original diagram operations and carrier cocone define
the cocone from which the lifted action is actually descended. -/
def tensorAlgebraActionCocone (c : Cocone (D ⋙ Algebra.forget O)) :
    Cocone ((D ⋙ Algebra.forget O) ⋙ profileEndofunctor O.toCollection) where
  pt := c.pt
  ι := tensorAlgebraDiagramActions O D ≫ c.ι

/-- The actual action on a given carrier colimit, using the proved
preservation of its original sifted tensor-profile colimit. -/
def tensorAlgebraColimitAction (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c) :
    profileCoinvariants O.toCollection c.pt ⟶ c.pt :=
  (isColimitOfPreserves (profileEndofunctor O.toCollection) hc).desc (tensorAlgebraActionCocone c)

omit [Small.{us} W] in
/-- Every original carrier injection preserves the constructed
action; this is the actual colimit descent equation. -/
theorem tensorAlgebraColimitAction_fac (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) (j : J) :
    profileMap O.toCollection (c.ι.app j) ≫ tensorAlgebraColimitAction c hc =
      (D.obj j).action ≫ c.ι.app j :=
  (isColimitOfPreserves (profileEndofunctor O.toCollection) hc).fac
    (tensorAlgebraActionCocone c) j

omit [Small.{us} W] in
/-- The constructed action satisfies the original unary unit,
proved after every original carrier colimit injection. -/
theorem tensorAlgebraColimitAction_unit (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) :
    (profileUnit O).app c.pt ≫ tensorAlgebraColimitAction c hc = 𝟙 c.pt := by
  apply hc.hom_ext
  intro j
  exact colimitUnitFromInjection (c.ι.app j)
    ((profileUnit O).app (D.obj j).carrier) ((profileUnit O).app c.pt)
    (profileMap O.toCollection (c.ι.app j)) (D.obj j).action
    (tensorAlgebraColimitAction c hc) ((profileUnit O).naturality (c.ι.app j))
    (tensorAlgebraColimitAction_fac c hc j) (D.obj j).action_unit

/-- The constructed action satisfies the actual profile
substitution equation. Double tensor-profile colimit injections
jointly detect it, and the original diagram algebra equations prove it. -/
theorem tensorAlgebraColimitAction_assoc (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) :
    profileMultiplication O c.pt ≫ tensorAlgebraColimitAction c hc =
      profileMap O.toCollection (tensorAlgebraColimitAction c hc) ≫
        tensorAlgebraColimitAction c hc := by
  refine (isColimitOfPreserves (profileEndofunctor O.toCollection)
    (isColimitOfPreserves (profileEndofunctor O.toCollection) hc)).hom_ext fun j => ?_
  have hm :
      profileMap O.toCollection (profileMap O.toCollection (c.ι.app j)) ≫
          profileMap O.toCollection (tensorAlgebraColimitAction c hc) =
        profileMap O.toCollection (D.obj j).action ≫ profileMap O.toCollection (c.ι.app j) :=
    (profileMap_comp O.toCollection _ _).symm.trans
      ((congrArg (fun f => profileMap O.toCollection f)
        (tensorAlgebraColimitAction_fac c hc j)).trans (profileMap_comp O.toCollection _ _))
  exact colimitAssocFromInjection (c.ι.app j) (profileMap O.toCollection (c.ι.app j))
    (profileMap O.toCollection (profileMap O.toCollection (c.ι.app j)))
    (D.obj j).action (tensorAlgebraColimitAction c hc)
    (profileMultiplication O (D.obj j).carrier) (profileMultiplication O c.pt)
    (profileMap O.toCollection (D.obj j).action)
    (profileMap O.toCollection (tensorAlgebraColimitAction c hc))
    ((profileMultiplicationNatTrans O).naturality (c.ι.app j))
    (tensorAlgebraColimitAction_fac c hc j) hm (D.obj j).action_assoc

/-- Every original operation on the given carrier colimit is
constructed from its actual descended action and profile injection.
The full original unit and substitution axioms have been proved. -/
def tensorAlgebraColimitPoint (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c) : Algebra O :=
  Algebra.ofAction O c.pt (tensorAlgebraColimitAction c hc)
    (tensorAlgebraColimitAction_unit c hc) (tensorAlgebraColimitAction_assoc c hc)

/-- Descending the constructed full operations recovers the
actual constructed carrier colimit action. -/
@[simp]
theorem tensorAlgebraColimitPoint_action (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) :
    (tensorAlgebraColimitPoint c hc).action = tensorAlgebraColimitAction c hc :=
  Algebra.ofAction_action O c.pt (tensorAlgebraColimitAction c hc)
    (tensorAlgebraColimitAction_unit c hc) (tensorAlgebraColimitAction_assoc c hc)

/-- The actual lifted cocone has precisely the given carrier
cocone injections, with all original operation squares constructed. -/
def tensorAlgebraLiftedCocone (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c) :
  Cocone D where
  pt := tensorAlgebraColimitPoint c hc
  ι :=
    { app := fun j => Algebra.Hom.ofActionEquation (D.obj j) (tensorAlgebraColimitPoint c hc)
        (c.ι.app j) (by
          exact (congrArg (fun k => profileMap O.toCollection (c.ι.app j) ≫ k)
            (Algebra.ofAction_action O c.pt (tensorAlgebraColimitAction c hc)
              (tensorAlgebraColimitAction_unit c hc) (tensorAlgebraColimitAction_assoc c hc))).trans
            (tensorAlgebraColimitAction_fac c hc j))
      naturality := fun i j f => by
        apply Algebra.Hom.ext
        change (D.map f).hom ≫ c.ι.app j = c.ι.app i ≫ 𝟙 _
        exact (c.w f).trans (Category.comp_id _).symm }

/-- The constructed operation at every original profile,
including the nullary profile, is exactly the original quotient
injection followed by the actual descended colimit action. -/
@[simp]
theorem tensorAlgebraColimitPoint_operation (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) (d : W) (P : AnalyticIndex W d) :
    (tensorAlgebraColimitPoint c hc).operations.app d P =
      profileι O.toCollection c.pt P ≫ tensorAlgebraColimitAction c hc d := rfl

/-- Every lifted injection is the given original carrier injection
at all colors. -/
@[simp]
theorem tensorAlgebraLiftedCocone_ι_hom (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) (j : J) :
    ((tensorAlgebraLiftedCocone c hc).ι.app j).hom = c.ι.app j := rfl


end CategoryTheory.Operad.Tensor
end
end
end source_TensorAlgebraSiftedLift


section source_TensorAlgebraSiftedCreation
/-!
## The original tensor algebra forgetful functor creates sifted colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us uJ vJ

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

private theorem colimitDescFromInjection {V : Type*} [Category* V]
    {A B TA TB X TX : V} (i : A ⟶ B) (ti : TA ⟶ TB) (a : TA ⟶ A) (b : TB ⟶ B)
    (f : B ⟶ X) (tf : TB ⟶ TX) (x : TX ⟶ X) (s : A ⟶ X) (ts : TA ⟶ TX)
    (hif : i ≫ f = s) (ht : ti ≫ tf = ts)
    (hx : ts ≫ x = a ≫ s) (hb : ti ≫ b = a ≫ i) :
    ti ≫ (tf ≫ x) = ti ≫ (b ≫ f) := by
  rw [← Category.assoc ti tf, ht, hx, ← Category.assoc ti b, hb,
    Category.assoc a i, hif]

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [∀ d : W, HasColimitsOfShape (AnalyticIndex W d) C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]
variable {J : Type uJ} [Category.{vJ} J] [IsSifted J] [EssentiallySmall.{us} J]
variable [HasColimitsOfShape J C]
variable {O : ColoredOperadObj W C} {D : J ⥤ Algebra O}

/-- Descending an arbitrary original algebra cocone's carrier
maps yields a map preserving every original tensor operation. -/
def tensorAlgebraLiftedDesc (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c)
    (s : Cocone D) : (tensorAlgebraLiftedCocone c hc).pt ⟶ s.pt :=
  Algebra.Hom.ofActionEquation _ _ (hc.desc ((Algebra.forget O).mapCocone s)) (by
    let f := hc.desc ((Algebra.forget O).mapCocone s)
    have hbase : profileMap O.toCollection f ≫ s.pt.action =
        tensorAlgebraColimitAction c hc ≫ f := by
      refine (isColimitOfPreserves (profileEndofunctor O.toCollection) hc).hom_ext fun j => ?_
      have ht : profileMap O.toCollection (c.ι.app j) ≫ profileMap O.toCollection f =
          profileMap O.toCollection (s.ι.app j).hom :=
        (profileMap_comp O.toCollection _ _).symm.trans
          (congrArg (fun k => profileMap O.toCollection k) (hc.fac ((Algebra.forget
            O).mapCocone s) j))
      exact colimitDescFromInjection (c.ι.app j) (profileMap O.toCollection (c.ι.app j))
        (D.obj j).action (tensorAlgebraColimitAction c hc) f (profileMap O.toCollection f)
        s.pt.action (s.ι.app j).hom (profileMap O.toCollection (s.ι.app j).hom)
        (hc.fac ((Algebra.forget O).mapCocone s) j) ht
        (Algebra.action_naturality (s.ι.app j)).symm (tensorAlgebraColimitAction_fac c hc j)
    exact hbase.trans (congrArg (fun k => k ≫ f) (tensorAlgebraColimitPoint_action c hc).symm))

/-- The actual lifted cocone is a colimit. Its universal maps are
the carrier descents above, with full original operation squares;
uniqueness follows from the given carrier colimit and faithful carriers. -/
def tensorAlgebraLiftedIsColimit (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c) :
    IsColimit (tensorAlgebraLiftedCocone c hc) where
  desc s := tensorAlgebraLiftedDesc c hc s
  fac s j := Algebra.Hom.ext (hc.fac ((Algebra.forget O).mapCocone s) j)
  uniq s m h := by
    apply Algebra.Hom.ext
    apply hc.hom_ext
    intro j
    exact (congrArg (fun f => f.hom) (h j)).trans
      (hc.fac ((Algebra.forget O).mapCocone s) j).symm

/-- Forgetting the actual lifted cocone returns precisely the
given original carrier cocone, through identity carrier components. -/
def tensorAlgebraLiftedValid (c : Cocone (D ⋙ Algebra.forget O)) (hc : IsColimit c) :
    (Algebra.forget O).mapCocone (tensorAlgebraLiftedCocone c hc) ≅ c :=
  Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)

/-- The original operation-map forgetful functor creates every
source-sized sifted colimit, with an explicitly constructed action,
all original operation maps, lifted injections, and universal maps.
Its premises are the source tensor commutation hypotheses. -/
instance tensorAlgebraForgetCreatesSiftedColimit (D : J ⥤ Algebra O) :
    CreatesColimit D (Algebra.forget O) :=
  createsColimitOfReflectsIso fun c hc =>
    { liftedCocone := tensorAlgebraLiftedCocone c hc
      validLift := tensorAlgebraLiftedValid c hc
      makesColimit := tensorAlgebraLiftedIsColimit c hc }

/-- All original diagrams of the source-sized sifted shape have
the explicitly constructed colimit lift. -/
instance tensorAlgebraForgetCreatesSiftedColimits (O : ColoredOperadObj W C) :
    CreatesColimitsOfShape J (Algebra.forget O) where
  CreatesColimit := tensorAlgebraForgetCreatesSiftedColimit _

/-- The universal map retains exactly the original carrier
colimit descent, at every original color. -/
@[simp]
theorem tensorAlgebraLiftedDesc_hom (c : Cocone (D ⋙ Algebra.forget O))
    (hc : IsColimit c) (s : Cocone D) :
    (tensorAlgebraLiftedDesc c hc s).hom = hc.desc ((Algebra.forget O).mapCocone s) := rfl


end CategoryTheory.Operad.Tensor
end
end
end source_TensorAlgebraSiftedCreation


section source_TensorAlgebraFilteredReflexive
/-!
## The source filtered colimits and reflexive pairs of tensor algebras
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us uJ vJ

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable {W : Type u} {C : Type w} [Category.{v} C] [FiniteTensor C]
variable [Small.{us} W] [HasColimitsOfSize.{us, us} C]
variable [FiniteTensorPreservesColimitsInEachSlot.{v, w, us} C]

local instance (d : W) : HasColimitsOfShape (AnalyticIndex W d) C :=
  hasProfileColimitsOfSmallColors C d

/-- The original tensor algebra forgetful functor creates every
filtered colimit of the source size. This is obtained from the actual
constructed sifted lift and the proved filtered diagonal property. -/
@[instance_reducible]
def tensorAlgebraForgetCreatesFilteredColimits {J : Type uJ} [Category.{vJ} J]
    [IsFiltered J] [EssentiallySmall.{us} J] (O : ColoredOperadObj W C) :
    CreatesColimitsOfShape J (Algebra.forget O) := by
  let : IsSifted J := IsFiltered.isSifted
  let : HasColimitsOfShape J C := HasColimitsOfShape.of_essentiallySmall C J
  exact tensorAlgebraForgetCreatesSiftedColimits O

/-- Reflexive pairs are the actual proved sifted shape, so their
colimits lift to all original tensor operation maps by the same
explicit carrier action and cocone construction. -/
@[instance_reducible]
def tensorAlgebraForgetCreatesReflexivePairs (O : ColoredOperadObj W C) :
    CreatesColimitsOfShape WalkingReflexivePair (Algebra.forget O) := by
  let : HasColimitsOfShape WalkingReflexivePair C :=
    HasColimitsOfShape.of_essentiallySmall C WalkingReflexivePair
  exact tensorAlgebraForgetCreatesSiftedColimits O

/-- The actual original reflexive pair, with its supplied common
section, has a coequalizer created by the original algebra forgetful
functor. The proved final inclusion identifies its actual parallel-pair
coforks with the constructed reflexive-pair colimit lift. -/
@[instance_reducible]
def tensorAlgebraForgetCreatesReflexiveCoequalizer (O : ColoredOperadObj W C)
    {A B : Algebra O} (f g : A ⟶ B) [IsReflexivePair f g] :
    CreatesColimit (parallelPair f g) (Algebra.forget O) := by
  let : CreatesColimitsOfShape WalkingReflexivePair (Algebra.forget O) :=
    tensorAlgebraForgetCreatesReflexivePairs O
  let : CreatesColimit
      (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ ofIsReflexivePair f g)
      (Algebra.forget O) := inferInstance
  exact createsColimitOfIsoDiagram (Algebra.forget O)
    (inclusionWalkingReflexivePairOfIsReflexivePairIso f g)


end CategoryTheory.Operad.Tensor
end
end
end source_TensorAlgebraFilteredReflexive
