/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralLiftedRamificationData

/-!
# The native category of admissible cameral torus bundles

Objects retain the actual T torsor, full scheme-valued normalizer shift,
the lifted beta isomorphisms and all three compatibility conditions.
Arrows are actual equivariant torsor arrows preserving gamma and beta
on every parameter scheme. Identity and composition are the native
torsor identity and composition, with completed preservation proofs.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 6.2--6.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralAdmissibleTorusBundles

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open ContractedTorsorModels ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)

attribute [local instance] CameralRamificationTensorModels.torusGroup

structure Object where
  bundle : Bundle (Torus F) (total F C)
  shift : ConstantNormalizerShift F K D R B bundle
  full : FullNormalizerShift F K D R B bundle shift
  beta : LiftedBetaMaps F K D R A B bundle
  compatibility : LiftedBetaCompatibility F K D R A B bundle beta shift Q E T

def parameterMap {L M : Bundle (Torus F) (total F C)} (a : L ⟶ M)
    (U : Over (Spec (.of ℂ))) :
    parameterBundle F K D B L U ⟶ parameterBundle F K D B M U :=
  (D.torus.baseChange.change (B.pulled U).arrow.total).map a

theorem parameterMap_comp {L M N : Bundle (Torus F) (total F C)} (a : L ⟶ M) (b : M ⟶ N)
    (U : Over (Spec (.of ℂ))) :
    parameterMap F K D B (a ≫ b) U = parameterMap F K D B a U ≫ parameterMap F K D B b U :=
  (D.torus.baseChange.change (B.pulled U).arrow.total).map_comp a b

structure Hom (P P' : Object F K D R A B Q E T) where
  map : P.bundle ⟶ P'.bundle
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w),
    (shiftFunctor F K D (B.pulled U).cover w).map (parameterMap F K D B map U) ≫
      (P'.shift.gamma U n w hn).hom =
    (P.shift.gamma U n w hn).hom ≫ parameterMap F K D B map U
  beta : ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
      (c : U ⟶ torusScheme ℂ 1),
    (P.beta.beta U i hi c).hom =
      (Scheme.Modules.pullback (fixedInclusion F (B.pulled U).cover i).left).map
        ((A.line (total F (B.pulled U).cover) i).map (parameterMap F K D B map U)) ≫
      (P'.beta.beta U i hi c).hom

@[ext] theorem Hom.ext {P P' : Object F K D R A B Q E T} (a b : Hom F K D R A B Q E T P P')
    (h : a.map = b.map) : a = b := by
  cases a
  cases b
  cases h
  rfl

def idHom (P : Object F K D R A B Q E T) : Hom F K D R A B Q E T P P where
  map := 𝟙 P.bundle
  gamma U n w hn := by
    dsimp only [parameterMap]
    rw [(D.torus.baseChange.change (B.pulled U).arrow.total).map_id]
    rw [(shiftFunctor F K D (B.pulled U).cover w).map_id]
    simp only [Category.id_comp, Category.comp_id]
  beta U i hi c := by
    dsimp only [parameterMap]
    rw [(D.torus.baseChange.change (B.pulled U).arrow.total).map_id,
      (A.line (total F (B.pulled U).cover) i).map_id,
      (Scheme.Modules.pullback (fixedInclusion F (B.pulled U).cover i).left).map_id,
      Category.id_comp]

def compHom {P P' P'' : Object F K D R A B Q E T}
    (a : Hom F K D R A B Q E T P P') (b : Hom F K D R A B Q E T P' P'') :
    Hom F K D R A B Q E T P P'' where
  map := a.map ≫ b.map
  gamma U n w hn := by
    rw [parameterMap_comp, _root_.CategoryTheory.Functor.map_comp,
      Category.assoc, b.gamma U n w hn, ← Category.assoc, a.gamma U n w hn, Category.assoc]
  beta U i hi c := by
    have ha := a.beta U i hi c
    have hb := b.beta U i hi c
    rw [ha, hb]
    simp only [parameterMap, _root_.CategoryTheory.Functor.map_comp, Category.assoc]

instance category : Category (Object F K D R A B Q E T) where
  Hom := Hom F K D R A B Q E T
  id := idHom F K D R A B Q E T
  comp := compHom F K D R A B Q E T
  id_comp := by
    intro P P' a
    apply Hom.ext
    exact Category.id_comp a.map
  comp_id := by
    intro P P' a
    apply Hom.ext
    exact Category.comp_id a.map
  assoc := by
    intro P P' P'' P''' a b c
    apply Hom.ext
    exact Category.assoc a.map b.map c.map

def forget : Object F K D R A B Q E T ⥤ Bundle (Torus F) (total F C) where
  obj P := P.bundle
  map a := a.map

instance forgetFaithful : (forget F K D R A B Q E T).Faithful where
  map_injective := fun {_P _P'} {a b} h => Hom.ext F K D R A B Q E T a b h

end MathlibExt.AlgebraicGeometry.CameralAdmissibleTorusBundles
