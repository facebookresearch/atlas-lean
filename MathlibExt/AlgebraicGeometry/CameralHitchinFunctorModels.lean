/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralHiggsCategoryModels
public import MathlibExt.AlgebraicGeometry.CameralCartanValueModels
public import MathlibExt.AlgebraicGeometry.CameralUniversalRawLiftModels

/-!
# The actual regularized Hitchin map and marked value fibres

The value is computed from the original c tensor K section by the
actual universal Borel quotient. Base arrows are W-equivariant cover
isomorphisms preserving the entire scheme-valued map. Higgs arrows
retain the original torsor, module and incidence maps. A fibre is the
actual category of objects with an isomorphism to the specified
cameral/value pair; its marking is the inverse of that same cover map.
The torus-fibre functor is the actual adapted B-to-T quotient functor.
Source: DG math/0005132v3, Theorem17.5/Section17.7/Corollary17.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralHitchinFunctorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralRamificationReindexing
open CameralCartanValueModels CameralHiggsCategoryModels
open CameralRamificationTensorModels CameralBorelLiftModels
open CameralRootSL2Sources CameralRamificationCocycles
open CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralLiftedNormalizerModels CameralChevalleyConventionModels
open CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralNormalizerShifts ContractedTorsorModels ExpansionParameterModels
open LineBundleTaskContracts AlgebraicLineBundleFamilies
open RelativeLambdaReindexing

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (K : TwistLine X)
  (S : SectionSpace X (cartanKModule F X K)) (W : CartanWeylAction F X K S)

attribute [local instance] centralizerGroupAction

structure ValueObject where
  cover : Cover F X
  map : total F cover ⟶ sectionTotal S
  over : map ≫ sectionProjection S = projection F cover
  weyl : ∀ w, (coverIso F cover w).hom ≫ map = map ≫ (W.action w).asIso.hom

structure ValueHom (b b' : ValueObject F K S W) where
  cover : b.cover.cover.scheme ≅ b'.cover.cover.scheme
  weyl : ∀ w, (b.cover.cover.action w).asIso.hom ≫ cover.hom =
    cover.hom ≫ (b'.cover.cover.action w).asIso.hom
  value : (Over.map X.hom).map cover.hom ≫ b'.map = b.map

@[ext] theorem valueHom_ext {b b' : ValueObject F K S W}
    (a a' : ValueHom F K S W b b') (h : a.cover = a'.cover) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

def valueId (b : ValueObject F K S W) : ValueHom F K S W b b where
  cover := Iso.refl _
  weyl := by simp
  value := by simp

def valueComp {b b' b'' : ValueObject F K S W}
    (a : ValueHom F K S W b b') (a' : ValueHom F K S W b' b'') :
    ValueHom F K S W b b'' where
  cover := a.cover ≪≫ a'.cover
  weyl w := by
    simp only [Iso.trans_hom, ← Category.assoc]
    rw [a.weyl, Category.assoc, a'.weyl, Category.assoc]
  value := by
    rw [Iso.trans_hom, Functor.map_comp, Category.assoc, a'.value, a.value]

instance valueCategory : Category (ValueObject F K S W) where
  Hom := ValueHom F K S W
  id := valueId F K S W
  comp := valueComp F K S W
  id_comp a := valueHom_ext F K S W _ _ (Iso.refl_trans a.cover)
  comp_id a := valueHom_ext F K S W _ _ (Iso.trans_refl a.cover)
  assoc a b c := valueHom_ext F K S W _ _ (Iso.trans_assoc a.cover b.cover c.cover)

def valueInverse {b b' : ValueObject F K S W} (a : b ⟶ b') : b' ⟶ b where
  cover := a.cover.symm
  weyl w := by
    apply (cancel_epi a.cover.hom).1
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ a.cover.inv) (a.weyl w).symm
  value := by
    rw [← a.value, ← Category.assoc, ← Functor.map_comp]
    simp

def valueIso {b b' : ValueObject F K S W} (a : b ⟶ b') : b ≅ b' where
  hom := a
  inv := valueInverse F K S W a
  hom_inv_id := by apply valueHom_ext; apply Iso.ext; exact a.cover.hom_inv_id
  inv_hom_id := by apply valueHom_ext; apply Iso.ext; exact a.cover.inv_hom_id

instance valueGroupoid : IsGroupoid (ValueObject F K S W) where
  all_isIso a := by
    let e := valueIso F K S W a
    exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

structure HiggsObject where
  bundle : RegularizedBundle F X K
  descent : CoverDescent F I bundle.regularizer
  quotient : CartanDescent F I bundle descent
  tensor : TensorPullbackComparison (projection F descent.cameral).left
  weyl : ∀ w, (coverIso F descent.cameral w).hom ≫
      valueMap F I bundle descent quotient tensor S =
    valueMap F I bundle descent quotient tensor S ≫ (W.action w).asIso.hom

@[implicit_reducible] def hitchinValue (H : HiggsObject F I K S W) :
    ValueObject F K S W where
  cover := H.descent.cameral
  map := valueMap F I H.bundle H.descent H.quotient H.tensor S
  over := valueMapOf_over F I H.bundle H.descent H.quotient H.tensor S H.bundle.sectionMap
  weyl := H.weyl

def incidencePoint (H : HiggsObject F I K S W) (U : Over (Spec (.of ℂ)))
    (c : U ⟶ total F H.descent.cameral) (p : U ⟶ H.bundle.regularizer.torsor.total)
    (hp : c ≫ projection F H.descent.cameral = p ≫ H.bundle.regularizer.torsor.projection) :
    U ⟶ universalTotal F I :=
  pullback.lift c p hp ≫ incidenceMap F I H.bundle.regularizer H.descent

structure HiggsHom (H H' : HiggsObject F I K S W) where
  map : CameralRegularizedHiggsModels.Hom F H.bundle H'.bundle
  value : hitchinValue F I K S W H ⟶ hitchinValue F I K S W H'
  incidence : ∀ (U : Over (Spec (.of ℂ))) (c : U ⟶ total F H.descent.cameral)
      (p : U ⟶ H.bundle.regularizer.torsor.total)
      (hp : c ≫ projection F H.descent.cameral = p ≫ H.bundle.regularizer.torsor.projection)
      (hq : (c ≫ (Over.map X.hom).map value.cover.hom) ≫
          projection F H'.descent.cameral =
        (p ≫ map.regularizer.iso.hom) ≫ H'.bundle.regularizer.torsor.projection),
    incidencePoint F I K S W H U c p hp = incidencePoint F I K S W H' U
      (c ≫ (Over.map X.hom).map value.cover.hom) (p ≫ map.regularizer.iso.hom) hq

@[ext] theorem higgsHom_ext {H H' : HiggsObject F I K S W}
    (a b : HiggsHom F I K S W H H') (hM : a.map = b.map) (hV : a.value = b.value) : a = b := by
  cases a
  cases b
  cases hM
  cases hV
  rfl

variable (L : CategoryCoherence F (X := X) (K := K))

@[implicit_reducible] def higgsId (H : HiggsObject F I K S W) :
    HiggsHom F I K S W H H where
  map := idHom F L H.bundle
  value := 𝟙 _
  incidence U c p hp hq := by
    change incidencePoint F I K S W H U c p hp =
      incidencePoint F I K S W H U (c ≫ (Over.map X.hom).map (𝟙 _)) (p ≫ 𝟙 _) _
    simp only [incidencePoint, (Over.map X.hom).map_id, Category.comp_id]
    change pullback.lift c p hp ≫ incidenceMap F I H.bundle.regularizer H.descent =
      pullback.lift (c ≫ 𝟙 (total F H.descent.cameral)) p _ ≫
        incidenceMap F I H.bundle.regularizer H.descent
    simp only [Category.comp_id]

@[implicit_reducible] def higgsComp {H H' H'' : HiggsObject F I K S W}
    (a : HiggsHom F I K S W H H') (b : HiggsHom F I K S W H' H'') :
    HiggsHom F I K S W H H'' where
  map := compHom F L a.map b.map
  value := a.value ≫ b.value
  incidence U c p hp hq := by
    have hp' : (c ≫ (Over.map X.hom).map a.value.cover.hom) ≫
        projection F H'.descent.cameral =
      (p ≫ a.map.regularizer.iso.hom) ≫ H'.bundle.regularizer.torsor.projection := by
      have hh : (Over.map X.hom).map a.value.cover.hom ≫ projection F H'.descent.cameral =
          projection F H.descent.cameral := by
        apply Over.OverMorphism.ext
        exact a.value.cover.hom.w
      simpa only [Category.assoc, hh, a.map.regularizer.over] using hp
    have ha := a.incidence U c p hp hp'
    have hb := b.incidence U (c ≫ (Over.map X.hom).map a.value.cover.hom)
      (p ≫ a.map.regularizer.iso.hom) hp' (by
        change (c ≫ (Over.map X.hom).map
            (a.value.cover.hom ≫ b.value.cover.hom)) ≫
              projection F H''.descent.cameral =
            (p ≫ (a.map.regularizer.iso.hom ≫ b.map.regularizer.iso.hom)) ≫
              H''.bundle.regularizer.torsor.projection at hq
        simpa only [Functor.map_comp, Category.assoc] using hq)
    change incidencePoint F I K S W H U c p hp =
      incidencePoint F I K S W H'' U
        (c ≫ (Over.map X.hom).map (a.value.cover.hom ≫ b.value.cover.hom))
        (p ≫ (a.map.regularizer.iso.hom ≫ b.map.regularizer.iso.hom)) _
    simpa only [Functor.map_comp, Category.assoc] using ha.trans hb

theorem higgs_id_comp {H H' : HiggsObject F I K S W}
    (a : HiggsHom F I K S W H H') :
    higgsComp F I K S W L (higgsId F I K S W L H) a = a := by
  apply higgsHom_ext
  · apply CameralHiggsCategoryModels.hom_ext
    · exact Category.id_comp a.map.regularizer
    · exact Iso.refl_trans a.map.adjoint
    · exact Iso.refl_trans a.map.centralizer
  · exact Category.id_comp a.value

theorem higgs_comp_id {H H' : HiggsObject F I K S W}
    (a : HiggsHom F I K S W H H') :
    higgsComp F I K S W L a (higgsId F I K S W L H') = a := by
  apply higgsHom_ext
  · apply CameralHiggsCategoryModels.hom_ext
    · exact Category.comp_id a.map.regularizer
    · exact Iso.trans_refl a.map.adjoint
    · exact Iso.trans_refl a.map.centralizer
  · exact Category.comp_id a.value

theorem higgs_assoc {H H' H'' H''' : HiggsObject F I K S W}
    (a : HiggsHom F I K S W H H') (b : HiggsHom F I K S W H' H'')
    (c : HiggsHom F I K S W H'' H''') :
    higgsComp F I K S W L (higgsComp F I K S W L a b) c =
      higgsComp F I K S W L a (higgsComp F I K S W L b c) := by
  apply higgsHom_ext
  · apply CameralHiggsCategoryModels.hom_ext
    · exact Category.assoc a.map.regularizer b.map.regularizer c.map.regularizer
    · exact Iso.trans_assoc a.map.adjoint b.map.adjoint c.map.adjoint
    · exact Iso.trans_assoc a.map.centralizer b.map.centralizer c.map.centralizer
  · exact Category.assoc a.value b.value c.value

@[instance_reducible] def higgsCategory : Category (HiggsObject F I K S W) where
  Hom := HiggsHom F I K S W
  id := higgsId F I K S W L
  comp := higgsComp F I K S W L
  id_comp := higgs_id_comp F I K S W L
  comp_id := higgs_comp_id F I K S W L
  assoc := higgs_assoc F I K S W L

def hitchinFunctor : letI := higgsCategory F I K S W L
    HiggsObject F I K S W ⥤ ValueObject F K S W := by
  letI := higgsCategory F I K S W L
  exact {
    obj := hitchinValue F I K S W
    map a := a.value
    map_id H := rfl
    map_comp a b := rfl }

structure FibreObject (b : ValueObject F K S W) where
  higgs : HiggsObject F I K S W
  comparison : hitchinValue F I K S W higgs ⟶ b

structure FibreHom {b : ValueObject F K S W} (H H' : FibreObject F I K S W b) where
  map : HiggsHom F I K S W H.higgs H'.higgs
  comparison : map.value ≫ H'.comparison = H.comparison

@[ext] theorem fibreHom_ext {b : ValueObject F K S W} {H H' : FibreObject F I K S W b}
    (a a' : FibreHom F I K S W H H') (h : a.map = a'.map) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

@[implicit_reducible] def fibreId {b : ValueObject F K S W}
    (H : FibreObject F I K S W b) :
    FibreHom F I K S W H H where
  map := higgsId F I K S W L H.higgs
  comparison := Category.id_comp _

@[implicit_reducible] def fibreComp {b : ValueObject F K S W}
    {H H' H'' : FibreObject F I K S W b}
    (a : FibreHom F I K S W H H') (a' : FibreHom F I K S W H' H'') :
    FibreHom F I K S W H H'' where
  map := higgsComp F I K S W L a.map a'.map
  comparison := by
    change (a.map.value ≫ a'.map.value) ≫ H''.comparison = H.comparison
    rw [Category.assoc, a'.comparison, a.comparison]

@[instance_reducible] def fibreCategory (b : ValueObject F K S W) :
    Category (FibreObject F I K S W b) where
  Hom := FibreHom F I K S W
  id := fibreId F I K S W L
  comp := fibreComp F I K S W L
  id_comp a := by
    apply fibreHom_ext
    exact higgs_id_comp F I K S W L a.map
  comp_id a := by
    apply fibreHom_ext
    exact higgs_comp_id F I K S W L a.map
  assoc a b c := by
    apply fibreHom_ext
    exact higgs_assoc F I K S W L a.map b.map c.map

@[implicit_reducible] def fibreMarked (b : ValueObject F K S W)
    (H : FibreObject F I K S W b) :
    Marked F I b.cover where
  regularizer := H.higgs.bundle.regularizer
  descent := H.higgs.descent
  marking := H.comparison.cover.symm
  weyl w := by
    apply (cancel_epi H.comparison.cover.hom).1
    simpa [hitchinValue, Category.assoc] using
      congrArg (fun f => f ≫ H.comparison.cover.inv) (H.comparison.weyl w).symm

/-- This is only the proof that the displayed original arrows preserve the inverse marking. -/
structure FibreArrowCoherence (b : ValueObject F K S W) : Prop where
  incidence : ∀ {H H' : FibreObject F I K S W b} (a : FibreHom F I K S W H H')
      (U : Over (Spec (.of ℂ))) (c : U ⟶ total F b.cover)
      (p : U ⟶ H.higgs.bundle.regularizer.torsor.total)
      (hp : p ≫ H.higgs.bundle.regularizer.torsor.projection = c ≫ projection F b.cover)
      (hq : (p ≫ a.map.map.regularizer.iso.hom) ≫
        H'.higgs.bundle.regularizer.torsor.projection = c ≫ projection F b.cover),
    CameralMarkedRegularizers.incidencePoint F I b.cover (fibreMarked F I K S W b H) U c p hp =
    CameralMarkedRegularizers.incidencePoint F I b.cover (fibreMarked F I K S W b H') U c
      (p ≫ a.map.map.regularizer.iso.hom) hq

def fibreMarkedFunctor (b : ValueObject F K S W) (P : FibreArrowCoherence F I K S W b) :
    letI := fibreCategory F I K S W L b
    FibreObject F I K S W b ⥤ Marked F I b.cover := by
  letI := fibreCategory F I K S W L b
  exact {
    obj := fibreMarked F I K S W b
    map := fun a => {
      map := a.map.map.regularizer
      incidence := fun U c p hp => P.incidence a U c p hp _ }
    map_id := fun H => by apply CameralMarkedRegularizers.Hom.ext; rfl
    map_comp := fun a a' => by apply CameralMarkedRegularizers.Hom.ext; rfl }

variable [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (N : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F N)
  (R : CanonicalRamificationFamily F N D) (A : CharacterCalculus F N D)
  (Q : SimpleReflectionTorsors F N D R) (E : RootWeylGeometry F N)
  (T : CanonicalSimpleRootTrivializations F N D R A)
  (BB : BorelGeometry F) (b : ValueObject F K S W)
  (B : ParameterCovers F b.cover) (NR : ReductionFamily F BB I b.cover)
  (O : BorelTorusOperations F BB)
  (Raw : RawLiftFamily F N D R A Q E T I BB B NR O)
  (Θ : ChevalleyComparison F N)
  (Ad : AdaptedLiftFamily F N D R A Q E T I BB B NR O Raw Θ)

def admissibleFibreFunctor (P : FibreArrowCoherence F I K S W b) :
    letI := fibreCategory F I K S W L b
    FibreObject F I K S W b ⥤ CameralAdmissibleTorusBundles.Object F N D R A B Q E T := by
  letI := fibreCategory F I K S W L b
  exact fibreMarkedFunctor F I K S W L b P ⋙
    admissibleFunctor F N D R A Q E T I BB B NR O Raw Θ Ad

end MathlibExt.AlgebraicGeometry.CameralHitchinFunctorModels
