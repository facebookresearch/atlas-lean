/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import MathlibExt.Algebra.Category.Grp.Monoidal
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.SheafificationCompat
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.MonoidalCore
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import MathlibExt.CategoryTheory.Localization.BousfieldCompat
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Tensor products, internal Hom, and restriction of module sheaves

Let `C : Type u` have morphism universe `u`, `J` be a Grothendieck topology, and `R : Sheaf J
CommRingCat.{u}`. Assume weak additive sheafification, the identification of its equivalences
with locally bijective maps, monoidality of `J.W`, and the underlying-ring sheaf comparison.
Module sheaves over the underlying ring sheaf form a monoidal closed category. Tensoring on
either side preserves colimits indexed by categories of object and morphism universe `u`.

Module sheafification is monoidal. The tensor of free sheaves on `A,B : Type u` is free on `A
× B`, with the canonical tensor-of-basis map. Tensor products of generating families have the
corresponding product index set.

For a slice site with the same monoidal sheafification and ring-comparison hypotheses,
restriction commutes with sheafification and has natural tensor comparisons. Their unit and
tensor identities are expressed through the adjunction and localization maps.
-/

@[expose] public section

universe v u

open _root_.CategoryTheory CategoryTheory MonoidalCategory Limits
open scoped _root_.AddCommGrpCat AddCommGrpCat
open scoped MonoidalCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}


namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})
variable [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Let `C : Type u` have morphism universe `u`, `J` be a topology, and `R : Sheaf J
CommRingCat.{u}`. Assume weak additive sheafification, `J.WEqualsLocallyBijective Ab.{u}`,
monoidality of `J.W`, and `J.HasSheafCompose (forget₂ CommRingCat RingCat)`. Then
`PresheafOfModules.sheafificationCommId R` is monoidal from module presheaves over `R.obj` to
module sheaves over the underlying ring sheaf of `R`. -/
noncomputable instance sheafificationCommIdMonoidal :
    (PresheafOfModules.sheafificationCommId R).Monoidal :=
  inferInstanceAs
    (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafificationCommId R)
      (J.W.inverseImage (PresheafOfModules.toPresheaf _)) (.refl _)).Monoidal

/-- Let `(C,J)` be a site with object, morphism, ring, and module universe `u`, and `R` a
commutative ring sheaf. Assume weak additive sheafification, the locally-bijective comparison,
monoidality of `J.W`, and the underlying-ring sheaf comparison. The category of module sheaves
over `R` is monoidal closed: for every `M`, tensoring `N ↦ M ⊗ N` has an internal-Hom right
adjoint, with `Hom(M ⊗ N,P) ≅ Hom(N,ihom(M,P))`. -/
noncomputable instance monoidalClosed :
    MonoidalClosed
      (SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)) :=
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (Sheaf.commRingCatForget₂Id R))

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. Put `L=PresheafOfModules.sheafificationCommId R`. For a module presheaf `A`,
there is a natural isomorphism `tensorLeft A ⋙ L ≅ L ⋙ tensorLeft L(A)`, whose component at
`B` identifies `L(A ⊗ B)` with `L(A) ⊗ L(B)` by the inverse monoidal tensor comparison. -/
noncomputable def tensorLeftSheafificationIso
    (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    tensorLeft A ⋙ PresheafOfModules.sheafificationCommId R ≅
      PresheafOfModules.sheafificationCommId R ⋙
        tensorLeft ((PresheafOfModules.sheafificationCommId R).obj A) :=
  _root_.CategoryTheory.NatIso.ofComponents
    (fun Y => (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (.refl _) A Y).symm)
    (by intro Y₁ Y₂ g
        exact (Localization.Monoidal.μ_inv_natural_right
          (PresheafOfModules.sheafificationCommId R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _) A g).symm)

/-- On a commutative ringed site `(C,J,R)` at common universe `u`, assume weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. Put `L=PresheafOfModules.sheafificationCommId R`. For any module presheaf
`A`, the functor `N ↦ L.obj A ⊗ N` preserves colimits of size `.{u,u}`, since it is left
adjoint to the internal-Hom functor. -/
noncomputable instance preservesColimitsOfSize_tensorLeft_sheafification
    (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
      (tensorLeft ((PresheafOfModules.sheafificationCommId R).obj A)) :=
  (ihom.adjunction _).leftAdjoint_preservesColimits

/-- On a commutative ringed site `(C,J,R)` at common universe `u`, assume weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. For any module sheaf `M`, the functor `N ↦ M ⊗ N` preserves colimits indexed
by categories with object and morphism universe `u`. -/
noncomputable instance preservesColimitsOfSize_tensorLeft
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- On a commutative ringed site `(C,J,R)` at common universe `u`, assume weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. For any module sheaf `M`, the functor `N ↦ N ⊗ M` preserves colimits of size
`.{u,u}`. The braiding identifies it naturally with left tensoring. -/
noncomputable instance preservesColimitsOfSize_tensorRight
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. The isomorphism `tensorUnitIso R : 𝟙_ ≅ SheafOfModules.unit R_ring`
identifies the monoidal tensor unit with the structure sheaf regarded as a module, where
`R_ring=(sheafCompose J (forget₂ ..)).obj R`. -/
noncomputable def tensorUnitIso :
    𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ _ _)).obj R) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
    (Sheaf.commRingCatForget₂Id R)).counit)).app
    (SheafOfModules.unit ((sheafCompose J (forget₂ _ _)).obj R))

namespace FreeTensor

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. Let `R_s` be the
underlying ring sheaf and `U_R=unit R_s`. For `A,B : Type u`, `a∈A`, and `b∈B`, `innerLeg R A
B a b : U_R ⊗ U_R → free_{R_s}(A × B)` is `(tensorUnitIso R).inv ⊗ 𝟙`, followed by the left
unitor and the basis inclusion `ιFree (a,b)`. -/
noncomputable def innerLeg (A B : Type u) (a : A) (b : B) :
    SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⊗
      SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫ SheafOfModules.ιFree (a, b)

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, monoidal `J.W`, and the locally-bijective and underlying-ring sheaf
comparisons. Write `R_s` for the underlying ring sheaf and `U_R=unit R_s`. For `A,B : Type u`,
`a∈A`, and `b∈B`, `outerLeg R A B a b : U_R → free_{R_s} A ⊗ free_{R_s} B` is the inverse left
unitor, followed by `tensorUnitIso R ⊗ 𝟙` and `ιFree a ⊗ ιFree b`. -/
noncomputable def outerLeg (A B : Type u) (a : A) (b : B) :
    SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
      SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
      SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B :=
  (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
    (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b)

/-- On a commutative ringed site `(C,J,R)` at universe `u`, assume weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring sheaf comparisons. For `A : Type
u` and `U_R=unit R_s`, the cofan with point `free_{R_s} A ⊗ U_R` and legs `ιFree a ⊗ 𝟙 U_R`,
indexed by `a∈A`, is a colimit cofan of copies of `U_R ⊗ U_R`. Here `R_s` is the underlying
ring sheaf of `R`. -/
noncomputable def innerIsColimit (A : Type u) :
    _root_.CategoryTheory.Limits.IsColimit (Cofan.mk
      ((tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).obj
        (SheafOfModules.free (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A))
      (fun a ↦ (tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
        (SheafOfModules.ιFree a))) :=
  isColimitCofanMkObjOfIsColimit _ _ _ (SheafOfModules.isColimitFreeCofan A)

/-- On a commutative ringed site `(C,J,R)` at universe `u`, assume weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
the cofan with point `free_{R_s} A ⊗ free_{R_s} B` and legs `𝟙 free_{R_s} A ⊗ ιFree b`,
indexed by `b∈B`, is a colimit cofan of copies of `free_{R_s} A ⊗ unit R_s`. Here `R_s` is the
underlying ring sheaf of `R`. -/
noncomputable def outerIsColimit (A B : Type u) :
    _root_.CategoryTheory.Limits.IsColimit (Cofan.mk
      ((tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).obj
        (SheafOfModules.free (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B))
      (fun b ↦ (tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
        (SheafOfModules.ιFree b))) :=
  isColimitCofanMkObjOfIsColimit _ _ _ (SheafOfModules.isColimitFreeCofan B)

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`
and `b∈B`, `innerDesc R A B b : free_{R_s} A ⊗ unit R_s → free_{R_s}(A × B)` is the unique
morphism whose composite with `ιFree a ⊗ 𝟙` is `innerLeg R A B a b` for every `a∈A`. Here
`R_s` is the underlying ring sheaf of `R`. -/
noncomputable def innerDesc (A B : Type u) (b : B) :
    (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).obj
      (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  Cofan.IsColimit.desc (innerIsColimit R A) (fun a ↦ innerLeg R A B a b)

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`forwardHom R A B : free_{R_s} A ⊗ free_{R_s} B → free_{R_s}(A × B)` descends from the
second-index cofan, with component at `b` equal to `innerDesc R A B b`. It sends the
tensor-basis inclusion at `(a,b)` to `ιFree (a,b)`. Here `R_s` is the underlying ring sheaf of
`R`. -/
noncomputable def forwardHom (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  Cofan.IsColimit.desc (outerIsColimit R A B) (fun b ↦ innerDesc R A B b)

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`backwardHom R A B : free_{R_s}(A × B) → free_{R_s} A ⊗ free_{R_s} B` is the free-cofan
descendant whose component at `(a,b)` is `outerLeg R A B a b`. Here `R_s` is the underlying
ring sheaf of `R`. -/
noncomputable def backwardHom (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (A × B))
    (fun p ↦ outerLeg R A B p.1 p.2)

/-- On a commutative ringed site `(C,J,R)` at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons, let `A,B : Type u`
and `b∈B`. Then `(𝟙 free A ⊗ ιFree b) ≫ forwardHom R A B = innerDesc R A B b`, as maps `free A
⊗ unit R_s → free(A × B)`. Here `R_s` is the underlying ring sheaf of `R`. -/
theorem forwardHom_fac (A B : Type u) (b : B) :
    (tensorLeft (SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
      (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
  Cofan.IsColimit.fac (outerIsColimit R A B) _ b

/-- On a commutative ringed site `(C,J,R)` at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons, let `A,B : Type u`,
`a∈A`, and `b∈B`. Then `(ιFree a ⊗ 𝟙 unit R_s) ≫ innerDesc R A B b = innerLeg R A B a b`, as
maps from `unit R_s ⊗ unit R_s` to `free(A × B)`. Here `R_s` is the underlying ring sheaf of
`R`. -/
theorem innerDesc_fac (A B : Type u) (a : A) (b : B) :
    (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
      (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
  Cofan.IsColimit.fac (innerIsColimit R A) _ a

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. Write `R_s` for the
underlying ring sheaf. For `A,B : Type u` and `p∈A×B`, `ιFree p ≫ backwardHom R A B = outerLeg
R A B p.1 p.2`, as maps from `unit R_s` to `free A ⊗ free B`. -/
theorem backwardHom_fac (A B : Type u) (p : A × B) :
    SheafOfModules.ιFree p ≫ backwardHom R A B = outerLeg R A B p.1 p.2 :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ p

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`a∈A`, and `b∈B`, `outerLeg R A B a b ≫ forwardHom R A B = ιFree (a,b)`, the basis inclusion
into the free sheaf on `A×B` over the underlying ring sheaf. -/
@[simp]
theorem outerLeg_forwardHom (A B : Type u) (a : A) (b : B) :
    outerLeg R A B a b ≫ forwardHom R A B = SheafOfModules.ιFree (a, b) := by
  have h1 : (tensorLeft (SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
      (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
    Cofan.IsColimit.fac (outerIsColimit R A B) _ b
  have h2 : (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
      (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
    Cofan.IsColimit.fac (innerIsColimit R A) _ a
  have hT : (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) =
      (tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
        (SheafOfModules.ιFree a) ≫
      (tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
        (SheafOfModules.ιFree b) :=
    tensorHom_def _ _
  have hU : ((tensorUnitIso R).hom ⊗ₘ (𝟙 _
      : SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
        SheafOfModules.unit (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) ≫
      ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) = 𝟙 _ := by simp
  change (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
    (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) ≫ forwardHom R A B = _
  rw [hT]
  simp only [Category.assoc]
  rw [h1, h2]
  change (λ_ (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).inv ≫
    ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
      (((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫
        SheafOfModules.ιFree (a, b)) = _
  rw [← Category.assoc ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) _, hU,
    Category.id_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`a∈A`, and `b∈B`, `innerLeg R A B a b ≫ backwardHom R A B = ιFree a ⊗ ιFree b`, as maps from
`unit R_s ⊗ unit R_s` to `free A ⊗ free B`, where `R_s` is the underlying ring sheaf. -/
@[simp]
theorem innerLeg_backwardHom (A B : Type u) (a : A) (b : B) :
    innerLeg R A B a b ≫ backwardHom R A B =
      SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b := by
  have hfac : SheafOfModules.ιFree (a, b) ≫ backwardHom R A B = outerLeg R A B a b :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ (a, b)
  have hU : ((tensorUnitIso R).inv ⊗ₘ (𝟙 _
      : SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
        SheafOfModules.unit (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) ≫
      ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) = 𝟙 _ := by simp
  have hOuterLeg : outerLeg R A B a b = (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
      (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) := rfl
  change ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫ SheafOfModules.ιFree (a, b) ≫
    backwardHom R A B = _
  rw [hfac, hOuterLeg]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, hU, Category.id_comp]

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`forwardHom R A B ≫ backwardHom R A B = 𝟙 (free A ⊗ free B)`, with all free sheaves over the
underlying ring sheaf of `R`. -/
theorem forwardHom_backwardHom (A B : Type u) : forwardHom R A B ≫ backwardHom R A B = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (outerIsColimit R A B) _ _ (fun b ↦ ?_)
  change (tensorLeft (SheafOfModules.free (R := _) A)).map
      (SheafOfModules.ιFree b) ≫ (forwardHom R A B ≫ backwardHom R A B) =
    (tensorLeft (SheafOfModules.free (R := _) A)).map
      (SheafOfModules.ιFree b) ≫ 𝟙 _
  have hfacOut : (tensorLeft (SheafOfModules.free (R := _) A)).map
        (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
    Cofan.IsColimit.fac (outerIsColimit R A B) _ b
  have key : innerDesc R A B b ≫ backwardHom R A B =
      (tensorLeft (SheafOfModules.free (R := _) A)).map
        (SheafOfModules.ιFree b) := by
    refine Cofan.IsColimit.hom_ext (innerIsColimit R A) _ _ (fun a ↦ ?_)
    change (tensorRight (SheafOfModules.unit (R := _))).map
        (SheafOfModules.ιFree a) ≫ (innerDesc R A B b ≫ backwardHom R A B) =
      (tensorRight (SheafOfModules.unit (R := _))).map
        (SheafOfModules.ιFree a) ≫
        (tensorLeft (SheafOfModules.free (R := _) A)).map
          (SheafOfModules.ιFree b)
    have hfacIn : (tensorRight (SheafOfModules.unit (R := _))).map
          (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
      Cofan.IsColimit.fac (innerIsColimit R A) _ a
    rw [← Category.assoc, hfacIn, innerLeg_backwardHom]
    exact tensorHom_def _ _
  rw [← Category.assoc, hfacOut, key, Category.comp_id]

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`backwardHom R A B ≫ forwardHom R A B = 𝟙 free(A×B)`, with the free sheaf over the underlying
ring sheaf of `R`. -/
theorem backwardHom_forwardHom (A B : Type u) : backwardHom R A B ≫ forwardHom R A B = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (A × B)) _ _
    (fun p ↦ ?_)
  change SheafOfModules.ιFree p ≫ (backwardHom R A B ≫ forwardHom R A B) =
    SheafOfModules.ιFree p ≫ 𝟙 _
  have hfac : SheafOfModules.ιFree p ≫ backwardHom R A B = outerLeg R A B p.1 p.2 :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ p
  rw [← Category.assoc, hfac, outerLeg_forwardHom, Category.comp_id, Prod.mk.eta]

end FreeTensor

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For arbitrary `A,B
: Type u`, `freeTensorIso R A B : free_{R_s} A ⊗ free_{R_s} B ≅ free_{R_s}(A×B)` has forward
map `FreeTensor.forwardHom` and inverse `FreeTensor.backwardHom`, where `R_s` is the
underlying ring sheaf. -/
noncomputable def freeTensorIso (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B ≅
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) where
  hom := FreeTensor.forwardHom R A B
  inv := FreeTensor.backwardHom R A B
  hom_inv_id := FreeTensor.forwardHom_backwardHom R A B
  inv_hom_id := FreeTensor.backwardHom_forwardHom R A B

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`a∈A`, and `b∈B`, `FreeTensor.outerLeg R A B a b ≫ (freeTensorIso R A B).hom = ιFree (a,b)`,
the product-basis inclusion over the underlying ring sheaf. -/
theorem freeTensorIso_hom_basis (A B : Type u) (a : A) (b : B) :
    FreeTensor.outerLeg R A B a b ≫ (freeTensorIso R A B).hom =
      SheafOfModules.ιFree (a, b) :=
  FreeTensor.outerLeg_forwardHom R A B a b

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`
and `p∈A×B`, `ιFree p ≫ (freeTensorIso R A B).inv = FreeTensor.outerLeg R A B p.1 p.2`, the
tensor-basis inclusion over the underlying ring sheaf. -/
theorem freeTensorIso_inv_basis (A B : Type u) (p : A × B) :
    SheafOfModules.ιFree p ≫ (freeTensorIso R A B).inv =
      FreeTensor.outerLeg R A B p.1 p.2 :=
  FreeTensor.backwardHom_fac R A B p

namespace GeneratingSections

variable {M N : SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For
module sheaves `M,N` and generating families `G,H`, the map `G.π ⊗ H.π : free(G.I) ⊗ free(H.I)
→ M ⊗ N` is an epimorphism. The free sheaves are over the underlying ring sheaf of `R`. -/
theorem epi_tensorHom_π (G : M.GeneratingSections) (H : N.GeneratingSections) :
    Epi (G.π ⊗ₘ H.π) := by
  have : _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink _
  have : _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
      (tensorRight (SheafOfModules.free
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)) :=
    preservesColimitsOfSize_shrink _
  have e1 : Epi ((tensorRight (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)).map
      G.π) :=
    inferInstance
  have e2 : Epi ((tensorLeft M).map H.π) := inferInstance
  have h : G.π ⊗ₘ H.π =
      (tensorRight (SheafOfModules.free
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)).map
        G.π ≫
        (tensorLeft M).map H.π :=
    tensorHom_def _ _
  rw [h]
  exact inferInstance

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For arbitrary
generating families `G` of `M` and `H` of `N`, `GeneratingSections.tensor G H` generates `M ⊗
N` with index set `G.I × H.I`. Its presentation map is `(freeTensorIso R G.I H.I).inv ≫ (G.π ⊗
H.π)`. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.tensor (G : M.GeneratingSections)
    (H : N.GeneratingSections) :
    (M ⊗ N).GeneratingSections :=
  haveI : Epi (G.π ⊗ₘ H.π) := epi_tensorHom_π R G H
  haveI : Epi ((freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π)) :=
    epi_comp _ _
  (SheafOfModules.free.generatingSections (G.I × H.I)).ofEpi
    ((freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π))

/-- Under weak additive sheafification, monoidal `J.W`, and the locally-bijective and
underlying-ring comparisons on a commutative ringed site `(C,J,R)` at universe `u`, let `G,H`
generate module sheaves `M,N`. Then `(GeneratingSections.tensor G H).I = G.I × H.I`, as index
types. -/
@[simp]
theorem tensor_I (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).I = (G.I × H.I) :=
  rfl

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For generating
families `G,H` of module sheaves `M,N`, `tensorIndexEquiv R G H` identifies the tensor
family's index type with `G.I × H.I`, preserving each pair of generator indices. -/
def tensorIndexEquiv (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).I ≃ (G.I × H.I) :=
  Equiv.refl _

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For generating
families `G,H` and equivalences `eG : G.I ≃ Fin m`, `eH : H.I ≃ Fin n`, `tensorRankEquiv R G H
eG eH` gives `(GeneratingSections.tensor G H).I ≃ Fin (m*n)`. It counts the tensor generating
indices by the product of the two finite counts. -/
def tensorRankEquiv {m n : ℕ} (G : M.GeneratingSections) (H : N.GeneratingSections)
    (eG : G.I ≃ Fin m) (eH : H.I ≃ Fin n) :
    (tensor G (R := R) H).I ≃ Fin (m * n) :=
  (tensorIndexEquiv R G H).trans ((eG.prodCongr eH).trans finProdFinEquiv)

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For generating
families `G,H` of `M,N`, `(GeneratingSections.tensor G H).π = (freeTensorIso R G.I H.I).inv ≫
(G.π ⊗ H.π)` as maps `free(G.I × H.I) → M ⊗ N` over the underlying ring sheaf. -/
@[simp]
theorem tensor_π (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).π =
      (freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π) := by
  unfold _root_.SheafOfModules.GeneratingSections.tensor
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  exact Category.id_comp _

/-- Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For generating
families `G,H` of module sheaves `M,N`, if both `G.π` and `H.π` are isomorphisms, then
`(GeneratingSections.tensor G H).π` is an isomorphism presenting `M ⊗ N`. -/
instance tensor_isIso_π (G : M.GeneratingSections) (H : N.GeneratingSections)
    [IsIso G.π] [IsIso H.π] : IsIso (tensor G (R := R) H).π := by
  rw [tensor_π]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (MonoidalCategory.tensor_isIso _ _)

end GeneratingSections

end SheafOfModules

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})
variable [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

namespace RestrictSheafification

variable (X : C)

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
-- Stated above the site-variable blocks (with the `J`-level hypotheses
-- omitted) so no unneeded sheaf/monoidal hypotheses enter the signature
-- (the Mathlib whisker lemmas need none).
/-- Let `C : Type u` have morphism universe `u`, `J` be a Grothendieck topology, `X∈C`, and `f : P
→ Q` a morphism of `Ab.{u}`-valued presheaves on `C`. If `f` is locally injective for `J`,
then its precomposition by `(Over.forget X).op` is locally injective for `J.over X`. Local
injectivity means that equal image sections are equal after restriction along a covering
sieve. -/

instance whiskerIsLocallyInjective (P Q : Cᵒᵖ ⥤ Ab.{u}) (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective (J.over X) ((Over.forget X).op.whiskerLeft f) :=
  CategoryTheory.Presheaf.isLocallyInjective_whisker _ J _ f

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Let `C : Type u` have morphism universe `u`, `J` be a Grothendieck topology, `X∈C`, and `f : P
→ Q` a morphism of `Ab.{u}`-valued presheaves. If every target section locally lifts through
`f` for `J`, then the same local-surjectivity property holds after precomposition by
`(Over.forget X).op`, for `J.over X`. -/
instance whiskerIsLocallySurjective (P Q : Cᵒᵖ ⥤ Ab.{u}) (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective (J.over X) ((Over.forget X).op.whiskerLeft f) :=
  CategoryTheory.Presheaf.isLocallySurjective_whisker _ J _ f

variable [((J.over X).W (A := Ab.{u})).IsMonoidal] [(J.over X).WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify (J.over X) Ab.{u}]
variable [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- Let `C : Type u` have morphism universe `u`, `J` be a topology, `R : Sheaf J CommRingCat.{u}`,
and `X∈C`. The presheaf `overRing R X : (Over X)ᵒᵖ ⥤ RingCat.{u}` is the underlying ring
presheaf of `R.over X`. At an object `Y→X`, its ring is the underlying ring of `R(Y)`. -/
noncomputable abbrev overRing : (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  (Sheaf.over R X).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}
/-- Let `(C,J)` be a site at universe `u` and `R : Sheaf J CommRingCat.{u}`. Assuming
`J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})`, `sheafComposeRing R` is
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`, the sheaf obtained by forgetting
commutativity of the section rings. -/
noncomputable abbrev sheafComposeRing :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. Assuming the
underlying-ring sheaf comparison on `J.over X`, `overSheafComposeRing R X` is the underlying
ring sheaf of `R.over X`, namely `(sheafCompose (J.over X) (forget₂ CommRingCat RingCat)).obj
(Sheaf.over R X)`. -/
noncomputable abbrev overSheafComposeRing :=
  (sheafCompose (J.over X) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Sheaf.over R X)

/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. The functor
`restrictPresheaf R X` sends module presheaves over the underlying ring presheaf of `R` to
module presheaves over `overRing R X`. It precomposes the presheaf with `(Over.forget X).op`,
retaining the corresponding ring actions and restriction maps. -/
noncomputable abbrev restrictPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
    PresheafOfModules.{u} (overRing R X) :=
  PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj
/-- Let `(C,J)` be a site at universe `u` and `R : Sheaf J CommRingCat.{u}`. Assume weak additive
sheafification, `J.WEqualsLocallyBijective Ab.{u}`, and the underlying-ring sheaf comparison.
The functor `sheafificationBase R` is `PresheafOfModules.sheafificationCommId R`, from module
presheaves over `R.obj ⋙ forget₂ CommRingCat RingCat` to module sheaves over `sheafComposeRing
R`. -/
noncomputable abbrev sheafificationBase := PresheafOfModules.sheafificationCommId R
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. Assume weak
additive sheafification, the locally-bijective comparison, and the underlying-ring sheaf
comparison on `J.over X`. The functor `sheafificationOver R X` is `sheafificationCommId
(Sheaf.over R X)`, from module presheaves over `overRing R X` to module sheaves over
`overSheafComposeRing R X`. -/
noncomputable abbrev sheafificationOver := PresheafOfModules.sheafificationCommId (Sheaf.over R X)
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`, with
underlying-ring sheaf comparisons on the base and slice sites. The functor `restrictSheaf R X`
sends module sheaves over `sheafComposeRing R` to those over `overSheafComposeRing R X`. It is
`SheafOfModules.overFunctor (sheafComposeRing R) X`, with the canonical identification of the
target ring sheaves. -/
noncomputable abbrev restrictSheaf : SheafOfModules.{u} (sheafComposeRing R) ⥤
    SheafOfModules.{u} (overSheafComposeRing R X) :=
  SheafOfModules.overFunctor (sheafComposeRing R) X
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and assume the
underlying-ring sheaf comparison. Write `R_s=sheafComposeRing R` and `R_p=R.obj ⋙ forget₂
CommRingCat RingCat`. The functor `forgetRestrictBase R : SheafOfModules R_s →
PresheafOfModules R_p` forgets the sheaf structure and reindexes the ring action along
`Sheaf.commRingCatForget₂Id R`. -/
noncomputable abbrev forgetRestrictBase :=
  SheafOfModules.forget (sheafComposeRing R) ⋙
    PresheafOfModules.restrictScalars (CategoryTheory.Sheaf.commRingCatForget₂Id R)
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`, with the
underlying-ring sheaf comparison on `J.over X`. The functor `forgetRestrictOver R X` sends
module sheaves over `overSheafComposeRing R X` to module presheaves over `overRing R X`, by
forgetting and restricting scalars along `Sheaf.commRingCatForget₂Id (Sheaf.over R X)`. -/
noncomputable abbrev forgetRestrictOver :=
  SheafOfModules.forget (overSheafComposeRing R X) ⋙
    PresheafOfModules.restrictScalars
      (CategoryTheory.Sheaf.commRingCatForget₂Id (Sheaf.over R X))
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and assume weak additive
sheafification, the locally-bijective comparison, and the underlying-ring sheaf comparison.
The adjunction `sheafificationAdjBase R` is `sheafificationBase R ⊣ forgetRestrictBase R`,
formed using the identity ring comparison `Sheaf.commRingCatForget₂Id R`. -/
noncomputable abbrev sheafificationAdjBase := PresheafOfModules.sheafificationAdjunction
  (CategoryTheory.Sheaf.commRingCatForget₂Id R)
/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. Assume weak
additive sheafification, the locally-bijective comparison, and the underlying-ring sheaf
comparison on `J.over X`. Then `sheafificationAdjOver R X` is the adjunction
`sheafificationOver R X ⊣ forgetRestrictOver R X`. -/
noncomputable abbrev sheafificationAdjOver := PresheafOfModules.sheafificationAdjunction
  (CategoryTheory.Sheaf.commRingCatForget₂Id (Sheaf.over R X))

/-- Let `(C,J)` be a site at universe `u`, `R` a commutative ring sheaf, and `X∈C`, with
underlying-ring sheaf comparisons on the base and slice. For `S :
SheafOfModules(sheafComposeRing R)`, the isomorphism `forgetRestrictIso R X S` identifies
`restrictPresheaf R X (forgetRestrictBase R S)` with `forgetRestrictOver R X (restrictSheaf R
X S)`, as module presheaves over `overRing R X`. -/
noncomputable def forgetRestrictIso (S : SheafOfModules.{u} (sheafComposeRing R)) :
    (restrictPresheaf R X).obj ((forgetRestrictBase R).obj S) ≅
      (forgetRestrictOver R X).obj ((restrictSheaf R X).obj S) :=
  Iso.refl _

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
the locally-bijective comparison, and underlying-ring sheaf comparisons on the base and a
slice over `X`. Write `q_X=restrictPresheaf`, `F_X=restrictSheaf`, `L_R=sheafificationBase`,
and `U_X=forgetRestrictOver`. For a module presheaf `A`, `comparisonAdjoint R X A : q_X A →
U_X(F_X(L_R A))` is `q_X(η_A)` followed by `forgetRestrictIso` at `L_R A`, where `η` is the
base sheafification unit. -/
noncomputable def comparisonAdjoint :
    (restrictPresheaf R X).obj A ⟶
      (forgetRestrictOver R X).obj ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) :=
  (restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A) ≫
    (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
the locally-bijective comparison, and underlying-ring sheaf comparisons on the base and the
slice over `X`. For a module presheaf `A`, `comparisonHom R X A : sheafificationOver R X
(restrictPresheaf R X A) → restrictSheaf R X (sheafificationBase R A)` is the mate of
`comparisonAdjoint R X A` under the slice sheafification adjunction. -/
noncomputable def comparisonHom :
    (sheafificationOver R X).obj ((restrictPresheaf R X).obj A) ⟶
      (restrictSheaf R X).obj ((sheafificationBase R).obj A) :=
  ((sheafificationAdjOver R X).homEquiv _ _).symm (comparisonAdjoint R X A)

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
the locally-bijective comparison, and underlying-ring sheaf comparisons on the base and slice
over `X`. Put `L_X=sheafificationOver R X` and `F_X=restrictSheaf R X`. For each module
presheaf `A`, `comparisonHom R X A = L_X(comparisonAdjoint R X A) ≫ ε_{F_X(sheafificationBase
R A)}`, where `ε` is the counit of `sheafificationAdjOver R X`. -/
theorem comparisonHom_eq :
    comparisonHom R X A =
      (sheafificationOver R X).map (comparisonAdjoint R X A) ≫
        (sheafificationAdjOver R X).counit.app
            ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) :=
  (sheafificationAdjOver R X).homEquiv_counit _ _ _

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [((J.over X).W (A := Ab.{u})).IsMonoidal]
  [(J.over X).WEqualsLocallyBijective Ab.{u}] [HasWeakSheafify (J.over X) Ab.{u}] in
/-- Let `(C,J)` be a site at universe `u`, `R` a commutative ring sheaf, and `X∈C`, with
underlying-ring sheaf comparisons on the base and slice. Write `q_X=restrictPresheaf`,
`U_R=forgetRestrictBase`, `U_X=forgetRestrictOver`, `F_X=restrictSheaf`, and
`i_S=forgetRestrictIso R X S`. For `f : S → T` between module sheaves, `i_S.hom ≫ U_X(F_X(f))
= q_X(U_R(f)) ≫ i_T.hom`. -/
theorem forgetRestrictIso_naturality {S T : SheafOfModules.{u} (sheafComposeRing R)} (f : S ⟶ T) :
    (forgetRestrictIso R X S).hom ≫ (forgetRestrictOver R X).map ((restrictSheaf R X).map f) =
      (restrictPresheaf R X).map ((forgetRestrictBase R).map f) ≫
        (forgetRestrictIso R X T).hom := rfl

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [((J.over X).W (A := Ab.{u})).IsMonoidal] [HasWeakSheafify (J.over X) Ab.{u}]
  [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Let `C : Type u` have morphism universe `u`, `J` be a topology, `X∈C`, and `P : Cᵒᵖ ⥤ Ab.{u}`.
Assume weak additive sheafification on `J` and the locally-bijective characterization of `W`
on both `J` and `J.over X`. Then precomposition of `toSheafify J P` by `(Over.forget X).op`
belongs to `(J.over X).W`. Thus the restricted sheafification unit is a local equivalence on
the slice. -/
theorem whiskerToSheafify_memW (P : Cᵒᵖ ⥤ Ab.{u}) :
    (J.over X).W ((Over.forget X).op.whiskerLeft (CategoryTheory.toSheafify J P)) :=
  -- Whiskering preserves local bijectivity of the sheafification unit.

  GrothendieckTopology.W_of_isLocallyBijective _ _

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal]
  [HasWeakSheafify (J.over X) Ab.{u}]
  [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
theorem comparisonAdjoint_memW : (J.over X).W ((PresheafOfModules.toPresheaf _).map
    ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A))) := by
  have h1 : (PresheafOfModules.toPresheaf _).map ((sheafificationAdjBase R).unit.app A) =
      CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A) := rfl
  have h2 : (PresheafOfModules.toPresheaf _).map
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) =
      (Over.forget X).op.whiskerLeft
        ((PresheafOfModules.toPresheaf _).map ((sheafificationAdjBase R).unit.app A)) := rfl
  rw [h2, h1]
  have hLI : Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)) :=
    inferInstance
  have hLS : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)) :=
    inferInstance
  -- The whiskered unit is locally injective and locally surjective.
  have hWLI : Presheaf.IsLocallyInjective (J.over X)
      ((Over.forget X).op.whiskerLeft
        (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))) :=
    CategoryTheory.Presheaf.isLocallyInjective_whisker (J.over X) J
      (Over.forget X)
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))
  have hWLS : Presheaf.IsLocallySurjective (J.over X)
      ((Over.forget X).op.whiskerLeft
        (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))) :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker (J.over X) J
      (Over.forget X)
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))
  exact GrothendieckTopology.W_of_isLocallyBijective (J.over X)
    ((Over.forget X).op.whiskerLeft
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)))

instance :
    IsIso ((sheafificationOver R X).map
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A))) := by
  have hW : ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf _))
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) :=
    comparisonAdjoint_memW R X A
  exact Localization.inverts (sheafificationOver R X)
    ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf _)) _ hW

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
theorem comparisonAdjoint_map :
    (sheafificationOver R X).map (comparisonAdjoint R X A) =
      (sheafificationOver R X).map
          ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) ≫
        (sheafificationOver R X).map
          (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom := by
  unfold comparisonAdjoint
  rw [Functor.map_comp]

instance : IsIso ((sheafificationOver R X).map (comparisonAdjoint R X A)) := by
  rw [comparisonAdjoint_map]
  infer_instance

instance : IsIso (comparisonHom R X A) := by
  rw [comparisonHom_eq]
  infer_instance

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
theorem comparisonHom_natural {A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (h : A ⟶ B) :
    (sheafificationOver R X).map ((restrictPresheaf R X).map h) ≫ comparisonHom R X B =
      comparisonHom R X A ≫ (restrictSheaf R X).map ((sheafificationBase R).map h) := by
  have hunit : h ≫ (sheafificationAdjBase R).unit.app B =
      (sheafificationAdjBase R).unit.app A ≫
          (forgetRestrictBase R).map ((sheafificationBase R).map h) := by
    have h0 := (sheafificationAdjBase R).unit.naturality h
    simp only [Functor.id_map, _root_.CategoryTheory.Functor.comp_map] at h0
    exact h0
  have hcounit : (sheafificationOver R X).map
      ((forgetRestrictOver R X).map ((restrictSheaf R X).map ((sheafificationBase R).map h))) ≫
        (sheafificationAdjOver R X).counit.app
            ((restrictSheaf R X).obj ((sheafificationBase R).obj B)) =
      (sheafificationAdjOver R X).counit.app
          ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) ≫
        (restrictSheaf R X).map ((sheafificationBase R).map h) := by
    have h0 := (sheafificationAdjOver R X).counit.naturality
        ((restrictSheaf R X).map ((sheafificationBase R).map h))
    simp only [_root_.CategoryTheory.Functor.comp_map, Functor.id_map] at h0
    exact h0
  have key : (restrictPresheaf R X).map h ≫ comparisonAdjoint R X B =
      comparisonAdjoint R X A ≫
        (forgetRestrictOver R X).map ((restrictSheaf R X).map ((sheafificationBase R).map h)) := by
    unfold comparisonAdjoint
    rw [← Category.assoc _ _
      (forgetRestrictIso R X ((sheafificationBase R).obj B)).hom,
      ← Functor.map_comp, hunit, Functor.map_comp,
      Category.assoc _ (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom _,
      forgetRestrictIso_naturality,
      Category.assoc]
  simp only [comparisonHom_eq, Category.assoc]
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp, key, Functor.map_comp,
    Category.assoc]
  rw [hcounit]

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, and underlying-ring sheaf comparisons on the
base and the slice over `X`. There is a natural isomorphism `restrictPresheaf R X ⋙
sheafificationOver R X ≅ sheafificationBase R ⋙ restrictSheaf R X`. Its component at a module
presheaf `A` is the isomorphism with forward map `comparisonHom R X A`. -/
noncomputable def commIso : (restrictPresheaf R X) ⋙ (sheafificationOver R X) ≅
    (sheafificationBase R) ⋙ (restrictSheaf R X) :=
  _root_.CategoryTheory.NatIso.ofComponents (fun A => asIso (comparisonHom R X A))
    (fun {A B} h => by
    have hn := comparisonHom_natural R X h
    simpa only [_root_.CategoryTheory.Functor.comp_map, asIso_hom] using hn)

/-- Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. The
module-presheaf restriction `q_X=restrictPresheaf R X` is monoidal by pointwise
precomposition. It identifies `q_X(A) ⊗ q_X(B)` with `q_X(A ⊗ B)` and the slice's
structure-module presheaf with the restriction of the base structure-module presheaf. -/
noncomputable instance pfMonoidal : (restrictPresheaf R X).Monoidal :=
  inferInstanceAs
    ((PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal)

/-- Let `(C,J)` be a site at universe `u`, `R` a commutative ring sheaf, and `X∈C`, with the
underlying-ring sheaf comparison on the base. Assume weak additive sheafification, the
locally-bijective comparison, monoidality of `W`, and the underlying-ring sheaf comparison on
`J.over X`. The category of module sheaves over `(sheafComposeRing R).over X` is monoidal,
using its identification with the underlying ring sheaf of `R.over X`. -/
noncomputable instance overMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} ((sheafComposeRing R).over X)) :=
  inferInstanceAs (MonoidalCategory (SheafOfModules.{u} (overSheafComposeRing R X)))

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`. Assume weak additive
sheafification, the locally-bijective comparison, monoidality of `W`, and underlying-ring
sheaf comparisons on the base and slice over `X`. The functor `restrictSheaf R X` is monoidal.
Its structure descends from the monoidal composite of presheaf restriction and slice
sheafification through the natural isomorphism `commIso R X`. -/
noncomputable instance ofMonoidal : (restrictSheaf R X).Monoidal := by
  haveI : (sheafificationBase R).Monoidal :=
    inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (.refl _)).Monoidal)
  haveI : (sheafificationOver R X).Monoidal :=
    inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationOver R X)
      ((J.over X).W.inverseImage
        (PresheafOfModules.toPresheaf (overRing R X)))
      (.refl _)).Monoidal)
  haveI : Localization.Lifting (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictPresheaf R X ⋙ sheafificationOver R X) (restrictSheaf R X) :=
    ⟨(commIso R X).symm⟩
  exact Localization.Monoidal.functorMonoidalOfComp (sheafificationBase R)
    (J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
    (restrictSheaf R X) (restrictPresheaf R X ⋙ sheafificationOver R X)

/-- Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. The functor `sheafificationBase R` has the monoidal structure induced by
localization of module presheaves at the maps whose underlying additive presheaf maps belong
to `J.W`. -/
private noncomputable instance chainBaseMonoidal : (sheafificationBase R).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationBase R)
    (J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
    (.refl _)).Monoidal)

private noncomputable instance chainOverMonoidal : (sheafificationOver R X).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationOver R X)
    ((J.over X).W.inverseImage
      (PresheafOfModules.toPresheaf (overRing R X)))
    (.refl _)).Monoidal)

private noncomputable instance chainLift :
    Localization.Lifting (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictPresheaf R X ⋙ sheafificationOver R X) (restrictSheaf R X) :=
  ⟨(commIso R X).symm⟩

/-- Let `D` be any category, `U,V,W∈D`, `p : U ≅ V`, `X : U ≅ W`, and `Z : V ≅ W`. If `p.symm ≪≫ X
= Z` as isomorphisms from `V` to `W`, then `X = p ≪≫ Z` as isomorphisms from `U` to `W`. -/
private theorem cancel_symm_left {D : Type*} [Category* D] {U V W : D}
    (p : U ≅ V) (X : U ≅ W) (Z : V ≅ W) (h : p.symm ≪≫ X = Z) :
    X = p ≪≫ Z := by
  calc X = p ≪≫ (p.symm ≪≫ X) := by simp
    _ = p ≪≫ Z := by rw [h]

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For module
presheaves `A,B`, the structural tensor isomorphism `μ_{L_R}(A,B) : L_R(A) ⊗ L_R(B) ≅ L_R(A ⊗
B)` equals the localization tensor isomorphism at the class `J.W.inverseImage(toPresheaf)`,
where `L_R=sheafificationBase R`. -/
private theorem μ_base_eq (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    (Functor.Monoidal.μIso (sheafificationBase R) A B) =
      Localization.Monoidal.μ (sheafificationBase R)
        (J.W.inverseImage
          (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
        (.refl _) A B := rfl

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Let `(C,J)` be a site at universe `u`, `R` a commutative ring sheaf, and `X∈C`. Assume weak
additive sheafification, monoidal `W`, and the locally-bijective and underlying-ring
comparisons on `J.over X`. For module presheaves `A,B` over `overRing R X`, the structural
tensor isomorphism of `L_X=sheafificationOver R X` equals its localization tensor isomorphism
at `(J.over X).W.inverseImage(toPresheaf)`. -/
private theorem μ_over_eq (A B : PresheafOfModules.{u} (overRing R X)) :
    (Functor.Monoidal.μIso (sheafificationOver R X) A B) =
      Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage
          (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _) A B := rfl

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`X`. Write `F=restrictSheaf R X`, `L=sheafificationBase R`, `U=forgetRestrictBase R`, and `c_M
: L(U M) ≅ M` for the counit. For module sheaves `M,N`, `μ_F(M,N) ≪≫ F(c_M⁻¹ ⊗ c_N⁻¹) =
(F(c_M⁻¹) ⊗ F(c_N⁻¹)) ≪≫ μ_F(L(U M),L(U N))`. -/
private theorem μIso_conj (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    Functor.Monoidal.μIso (restrictSheaf R X) M N ≪≫
        (restrictSheaf R X).mapIso
          (MonoidalCategory.tensorIso
            (asIso ((sheafificationAdjBase R).counit.app M)).symm
            (asIso ((sheafificationAdjBase R).counit.app N)).symm) =
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      Functor.Monoidal.μIso (restrictSheaf R X) _ _ := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.tensorIso_hom,
    Functor.Monoidal.μIso_hom]
  exact (Functor.LaxMonoidal.μ_natural (restrictSheaf R X)
    (asIso ((sheafificationAdjBase R).counit.app M)).symm.hom
    (asIso ((sheafificationAdjBase R).counit.app N)).symm.hom).symm

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`X`. Put `L=sheafificationBase`, `T=sheafificationOver`, `q=restrictPresheaf`,
`F=restrictSheaf`, and `e_A : T(q A) ≅ F(L A)` for `commIso`. For module presheaves `A,B`,
`μ_F(L A,L B) = (e_A⁻¹ ⊗ e_B⁻¹) ≪≫ μ_{q⋙T}(A,B) ≪≫ e_{A⊗B} ≪≫ F(μ_L(A,B))⁻¹`. -/
private theorem μIso_sheafified (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    Functor.Monoidal.μIso (restrictSheaf R X)
      ((sheafificationBase R).obj A) ((sheafificationBase R).obj B) =
    MonoidalCategory.tensorIso
      (((commIso R X).symm).app A) (((commIso R X).symm).app B) ≪≫
    Functor.Monoidal.μIso
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B ≪≫
    ((((commIso R X).symm).app (A ⊗ B)).symm) ≪≫
    ((restrictSheaf R X).mapIso
      (Functor.Monoidal.μIso (sheafificationBase R) A B)).symm := by
  have p6h : (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj A) ((sheafificationBase R).obj B)).hom =
      (((commIso R X).symm.hom.app A) ⊗ₘ
        ((commIso R X).symm.hom.app B)) ≫
      (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X) A B).hom ≫
      ((commIso R X).symm.inv.app (A ⊗ B)) ≫
      (restrictSheaf R X).map
        (Functor.OplaxMonoidal.δ (sheafificationBase R) A B) :=
    Localization.Monoidal.functorMonoidalOfComp_μ
      (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictSheaf R X)
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B
  have qA : ((((commIso R X).symm).app A).hom) =
      (((commIso R X).symm.hom.app A)) := rfl
  have qB : ((((commIso R X).symm).app B).hom) =
      (((commIso R X).symm.hom.app B)) := rfl
  have qAB : (((((commIso R X).symm).app (A ⊗ B)).symm).hom) =
      (((commIso R X).symm.inv.app (A ⊗ B))) := rfl
  have qδ : (((Functor.Monoidal.μIso (sheafificationBase R) A B).symm.hom)) =
      (Functor.OplaxMonoidal.δ (sheafificationBase R) A B) := rfl
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.tensorIso_hom,
    Functor.Monoidal.μIso_hom, ← Functor.mapIso_symm]
  rw [qA, qB, qAB, qδ]
  exact p6h

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Let `(C,J)` be a site at universe `u`, `R` a commutative ring sheaf, and `X∈C`, with weak
additive sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons
on the slice. For `q=restrictPresheaf R X`, `T=sheafificationOver R X`, and module presheaves
`A,B`, `μ_{q⋙T}(A,B) = μ_T(q A,q B) ≪≫ T(μ_q(A,B))`. -/
private theorem μIso_comp (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    Functor.Monoidal.μIso
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B =
    Functor.Monoidal.μIso (sheafificationOver R X) _ _ ≪≫
    (sheafificationOver R X).mapIso
      (Functor.Monoidal.μIso (restrictPresheaf R X) A B) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom]
  rfl

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`X`. For `F=restrictSheaf R X`, `ofUnitIso R X : F(𝟙_Base) ≅ 𝟙_Slice` is the inverse of the
structural monoidal unit isomorphism `εIso F`. -/
noncomputable def ofUnitIso :
    (restrictSheaf R X).obj (𝟙_ (SheafOfModules.{u} (sheafComposeRing R))) ≅
      𝟙_ (SheafOfModules.{u} (overSheafComposeRing R X)) :=
  (Functor.Monoidal.εIso (restrictSheaf R X)).symm

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`X`. For `F=restrictSheaf R X` and module sheaves `M,N`, `ofTensorIso R X M N : F(M ⊗ N) ≅
F(M) ⊗ F(N)` is the inverse of `Functor.Monoidal.μIso F M N`. -/
noncomputable def ofTensorIso (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (restrictSheaf R X).obj (M ⊗ N) ≅ (restrictSheaf R X).obj M ⊗ (restrictSheaf R X).obj N :=
  (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over `X`.
Write `L=sheafificationBase`, `T=sheafificationOver`, `q=restrictPresheaf`, `F=restrictSheaf`,
`U=forgetRestrictBase`, `e_A : T(q A) ≅ F(L A)` for `commIso`, and `c_M : L(U M) ≅ M` for the
counit. For `A=U M`, `B=U N`, the inverse tensor isomorphism `μ_F(M,N)⁻¹` is the composite
`F(c_M⁻¹ ⊗ c_N⁻¹) ≪≫ F(μ_L(A,B)) ≪≫ e_{A⊗B}⁻¹ ≪≫ T(μ_q(A,B))⁻¹ ≪≫ μ_T(q A,q B)⁻¹ ≪≫ (e_A ⊗ e_B) ≪≫
(F(c_M) ⊗ F(c_N))`.
Here `μ_L` and `μ_T` are the localized monoidal tensor isomorphisms. The composite runs from `F(M ⊗
N)` to `F(M) ⊗ F(N)`. -/
theorem ofTensorIso_symm_chain (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage
          (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N))) := by
  have sC := μIso_conj R X M N
  have hPsym : ((restrictSheaf R X).mapIso
            (MonoidalCategory.tensorIso
              (asIso ((sheafificationAdjBase R).counit.app M)).symm
              (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm ≪≫
        (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm ≪≫
        (MonoidalCategory.tensorIso
          ((restrictSheaf R X).mapIso
            (asIso ((sheafificationAdjBase R).counit.app M)).symm)
          ((restrictSheaf R X).mapIso
            (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm := by
    have h2 := congrArg Iso.symm sC
    simp only [Iso.trans_symm] at h2
    exact h2
  have hA : (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      (MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm :=
    cancel_symm_left _ _ _ hPsym
  have hBsymm : (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm =
      (restrictSheaf R X).mapIso
        (Functor.Monoidal.μIso (sheafificationBase R)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).symm).app
        (((forgetRestrictBase R).obj M) ⊗ ((forgetRestrictBase R).obj N))) ≪≫
      (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X)
        ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)).symm ≪≫
      (MonoidalCategory.tensorIso
        (((commIso R X).symm).app ((forgetRestrictBase R).obj M))
        (((commIso R X).symm).app ((forgetRestrictBase R).obj N))).symm := by
    have h2 := congrArg Iso.symm (μIso_sheafified R X
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
    simp only [Iso.trans_symm, Iso.symm_symm_eq] at h2
    exact h2
  have hGsymm : (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X)
        ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)).symm =
      ((sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))).symm ≪≫
      (Functor.Monoidal.μIso (sheafificationOver R X)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm := by
    have h2 := congrArg Iso.symm (μIso_comp R X
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
    simp only [Iso.trans_symm] at h2
    exact h2
  rw [hBsymm, hGsymm] at hA
  have pieceH2 : (restrictSheaf R X).mapIso
        (Functor.Monoidal.μIso (sheafificationBase R)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) =
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) :=
    congrArg _ (μ_base_eq R
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
  have pieceH3 : ((((commIso R X).symm).app
        (((forgetRestrictBase R).obj M) ⊗ ((forgetRestrictBase R).obj N)))) =
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) := rfl
  have pieceH5 : (Functor.Monoidal.μIso (sheafificationOver R X)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm =
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm :=
    congrArg Iso.symm (μ_over_eq R X
      ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
      ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N)))
  have pieceH6 : (MonoidalCategory.tensorIso
        (((commIso R X).symm).app ((forgetRestrictBase R).obj M))
        (((commIso R X).symm).app ((forgetRestrictBase R).obj N))).symm =
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) := rfl
  have pieceH7 : (MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm =
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N))) := rfl
  rw [pieceH2, pieceH3, pieceH5, pieceH6, pieceH7] at hA
  exact hA

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over `X`.
Write `L=sheafificationBase`, `T=sheafificationOver`, `q=restrictPresheaf`, `F=restrictSheaf`,
`U=forgetRestrictBase`, `e_A : T(q A) ≅ F(L A)` for `commIso`, and `c_M : L(U M) ≅ M` for the
counit. For `A=U M`, `B=U N`, let `χ : F(M ⊗ N) ≅ F(M) ⊗ F(N)` be the composite
`F(c_M⁻¹ ⊗ c_N⁻¹) ≪≫ F(μ_L(A,B)) ≪≫ e_{A⊗B}⁻¹ ≪≫ T(μ_q(A,B))⁻¹ ≪≫ μ_T(q A,q B)⁻¹ ≪≫ (e_A ⊗ e_B) ≪≫
(F(c_M) ⊗ F(c_N))`.
Here `μ_L` and `μ_T` are the localized monoidal tensor isomorphisms.

Then `(ofTensorIso R X M N).hom = χ.hom`, as morphisms from `F(M ⊗ N)` to `F(M) ⊗ F(N)`. -/
theorem ofTensorIso_hom_eq (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (ofTensorIso R X M N).hom =
      ((restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)))).hom := by
  have h := congrArg Iso.hom (ofTensorIso_symm_chain R X M N)
  exact h

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over `X`.
Write `L=sheafificationBase`, `T=sheafificationOver`, `q=restrictPresheaf`, `F=restrictSheaf`,
`U=forgetRestrictBase`, `e_A : T(q A) ≅ F(L A)` for `commIso`, and `c_M : L(U M) ≅ M` for the
counit. For `A=U M`, `B=U N`, let `χ : F(M ⊗ N) ≅ F(M) ⊗ F(N)` be the composite
`F(c_M⁻¹ ⊗ c_N⁻¹) ≪≫ F(μ_L(A,B)) ≪≫ e_{A⊗B}⁻¹ ≪≫ T(μ_q(A,B))⁻¹ ≪≫ μ_T(q A,q B)⁻¹ ≪≫ (e_A ⊗ e_B) ≪≫
(F(c_M) ⊗ F(c_N))`.
Here `μ_L` and `μ_T` are the localized monoidal tensor isomorphisms.

Then `(ofTensorIso R X M N).inv = χ.inv`, as morphisms from `F(M) ⊗ F(N)` to `F(M ⊗ N)`. Thus
the inverse traverses the displayed isomorphism chain in reverse. -/
theorem ofTensorIso_inv_eq (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (ofTensorIso R X M N).inv =
      ((restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)))).inv := by
  have h := congrArg Iso.inv (ofTensorIso_symm_chain R X M N)
  exact h

end RestrictSheafification

end SheafOfModules

end
