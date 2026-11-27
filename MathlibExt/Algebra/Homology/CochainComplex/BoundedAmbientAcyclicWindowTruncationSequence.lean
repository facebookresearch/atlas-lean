/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindowTruncationFunctor
public import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequence

/-!
# Top-truncation cofiber sequences of exact functors

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Suppose F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. In the F-acyclic [a,b] window, use
degreewise admissible cofibrations and isomorphism weak maps.

The selected top kernel T_b(K), original complex K and top identity disk D_b(K) have the natural
row T_b(K)→K→D_b(K). Its degreewise rows are source conflations, and D_b(K) is the actual
pushout of the kernel inclusion along T_b(K)→0. Thus this is an objectwise Waldhausen cofiber
sequence.

For any map f:K→L, the selected base P_f=K⊔_(T_b K)T_b L has its old and new-kernel legs,
conormal quotient to D_b(K) and natural corner to L. A cofibration f gives a cofibration corner.
These diagrams establish the Waldhausen cofiber-functor sequence T_b→identity→D_b with its
specified natural maps.

Source and ambient object and Hom universes remain independent; the zero in each pushout is the
selected zero of the actual window category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientWindowTruncation

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For every K,
κK≫πK=0. -/
theorem kernelInclusion_projection (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    (kernelInclusion F hKernelClosure a b).app K ≫ (diskProjection F a b).app K = 0 := by
  apply (ambientAcyclicWindowRaw F a b).map_injective
  exact TruncationAt.topTruncationRawι_projection (b := b) (a := a)
    (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. The maps κK,πK
form the short complex T_b(K)→K→D_b(K) in the window category. -/
abbrev shortKernel (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    ShortComplex (AmbientAcyclicWindow F a b) :=
  ShortComplex.mk ((kernelInclusion F hKernelClosure a b).app K)
    ((diskProjection F a b).app K) (kernelInclusion_projection F hKernelClosure a b K)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. A map f:K→L
induces a morphism of these short complexes, with components T_b(f), f and D_b(f). -/
def shortKernelMap (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    shortKernel F hKernelClosure a b K ⟶ shortKernel F hKernelClosure a b L :=
  ShortComplex.homMk ((fullTruncationFunctor F hKernelClosure a b).map f) f
    ((diskFunctor F a b).map f)
    ((kernelInclusion F hKernelClosure a b).naturality f)
    ((diskProjection F a b).naturality f)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. Evaluating the
short kernel row in degree p gives T_b(K)ᵖ→Kᵖ→D_b(K)ᵖ as a short complex in E. -/
abbrev shortKernelTerm (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) : ShortComplex E :=
  (shortKernel F hKernelClosure a b K).map
    (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. In every degree
p, the row T_b(K)ᵖ→Kᵖ→D_b(K)ᵖ is an admissible exact sequence in E. -/
theorem shortKernelTerm_isAdmissibleExact (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) :
    IsAdmissibleExact (shortKernelTerm F hKernelClosure a b K p) :=
  TruncationAt.topTruncationRawShortComplex_term_isAdmissibleExact (b := b) (a := a)
    (hSupport := K.obj.property) F hKernelClosure K.obj.obj K.property p

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. Applying F to
every degree-p top-kernel row gives a short exact sequence in A. -/
theorem shortKernelTerm_map_shortExact (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) :
    ((shortKernelTerm F hKernelClosure a b K p).map F).ShortExact :=
  F.map_admissibleExact _ (shortKernelTerm_isAdmissibleExact F hKernelClosure a b K p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. Each whole kernel
inclusion κK:T_b(K)→K is a window cofibration. -/
theorem kernelInclusion_isCofibration (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsCofibration ((kernelInclusion F hKernelClosure a b).app K) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
  intro p
  exact isAdmissibleMono_f (shortKernelTerm_isAdmissibleExact F hKernelClosure a b K p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. In every degree
p, the image of the square T_b(K)→K, T_b(K)→0, K→D_b(K), 0→D_b(K) is a pushout in E. The zero is
the selected window zero and the right map is πK. -/
theorem zeroPushout_term (a b : ℤ) (K : AmbientAcyclicWindow F a b) (p : ℤ) :
    let G := ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p
    IsPushout (G.map (0 : (fullTruncationFunctor F hKernelClosure a b).obj K ⟶ 0))
      (G.map ((kernelInclusion F hKernelClosure a b).app K))
      (G.map (0 : (0 : AmbientAcyclicWindow F a b) ⟶ (diskFunctor F a b).obj K))
      (G.map ((diskProjection F a b).app K)) := by
  let G := ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p
  let S := shortKernelTerm F hKernelClosure a b K p
  obtain ⟨_, z, q, h⟩ := isCofibrationSequence_of_isAdmissibleExact
    (shortKernelTerm_isAdmissibleExact F hKernelClosure a b K p)
  have hz : z = 0 := (isZero_zero E).eq_of_tgt _ _
  have hq : q = 0 := (isZero_zero E).eq_of_src _ _
  rw [hz, hq] at h
  let e : G.obj (0 : AmbientAcyclicWindow F a b) ≅ (0 : E) :=
    (G.map_isZero (isZero_zero _)).isoZero
  apply h.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  all_goals simp

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. The square
T_b(K)→K, T_b(K)→0, K→D_b(K), 0→D_b(K), with right map πK and both zero maps, is a pushout after
forgetting to raw cochains. -/
theorem zeroPushout_raw (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    let R := ambientAcyclicWindowRaw F a b
    IsPushout (R.map (0 : (fullTruncationFunctor F hKernelClosure a b).obj K ⟶ 0))
      (R.map ((kernelInclusion F hKernelClosure a b).app K))
      (R.map (0 : (0 : AmbientAcyclicWindow F a b) ⟶ (diskFunctor F a b).obj K))
      (R.map ((diskProjection F a b).app K)) := by
  let R := ambientAcyclicWindowRaw F a b
  let c : PushoutCocone (0 : (fullTruncationFunctor F hKernelClosure a b).obj K ⟶
      (0 : AmbientAcyclicWindow F a b)) ((kernelInclusion F hKernelClosure a b).app K) :=
    PushoutCocone.mk 0 ((diskProjection F a b).app K) (by
      rw [zero_comp, kernelInclusion_projection])
  have hc : IsColimit (R.mapCocone c) := HomologicalComplex.isColimitOfEval _ _ (fun p =>
    (PushoutCocone.isColimitMapCoconeEquiv c
      (R ⋙ HomologicalComplex.eval E (.up ℤ) p)).symm
        (zeroPushout_term F hKernelClosure a b K p).isColimit)
  exact IsPushout.of_isColimit ((PushoutCocone.isColimitMapCoconeEquiv c R).1 hc)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. The disk D_b(K)
is the pushout of κK:T_b(K)→K along the zero map T_b(K)→0 in the actual window category. -/
theorem zeroPushout (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsPushout (0 : (fullTruncationFunctor F hKernelClosure a b).obj K ⟶
      (0 : AmbientAcyclicWindow F a b))
      ((kernelInclusion F hKernelClosure a b).app K)
      (0 : (0 : AmbientAcyclicWindow F a b) ⟶ (diskFunctor F a b).obj K)
      ((diskProjection F a b).app K) :=
  IsPushout.of_map_of_faithful (ambientAcyclicWindowRaw F a b)
    (zeroPushout_raw F hKernelClosure a b K)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. The natural maps
κK,πK give the objectwise Waldhausen cofiber sequence T_b(K)→K→D_b(K). -/
theorem objectwise_cofiberSequence (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsCofiberSequence ((kernelInclusion F hKernelClosure a b).app K)
      ((diskProjection F a b).app K) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  exact ⟨kernelInclusion_isCofibration F hKernelClosure a b K, 0, 0,
    zeroPushout F hKernelClosure a b K⟩

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For any f:K→L,
the span κK:T_b(K)→K and T_b(f):T_b(K)→T_b(L) has a pushout, since κK is a cofibration. -/
theorem base_hasPushout (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    HasPushout ((kernelInclusion F hKernelClosure a b).app K)
      ((fullTruncationFunctor F hKernelClosure a b).map f) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  obtain ⟨_, _, _, h, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
    ((kernelInclusion F hKernelClosure a b).app K)
    (kernelInclusion_isCofibration F hKernelClosure a b K)
    ((fullTruncationFunctor F hKernelClosure a b).obj L)
    ((fullTruncationFunctor F hKernelClosure a b).map f)
  exact h.flip.hasPushout

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. This
selected pushout is the base object of the naturality square for κ. -/
abbrev base (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    AmbientAcyclicWindow F a b :=
  letI := base_hasPushout F hKernelClosure a b f
  pushout ((kernelInclusion F hKernelClosure a b).app K)
    ((fullTruncationFunctor F hKernelClosure a b).map f)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
old-complex leg is u:K→P_f. -/
def baseInOld (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    K ⟶ base F hKernelClosure a b f :=
  letI := base_hasPushout F hKernelClosure a b f
  pushout.inl _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
new-kernel leg is v:T_b(L)→P_f. -/
def baseInKernel (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    (fullTruncationFunctor F hKernelClosure a b).obj L ⟶ base F hKernelClosure a b f :=
  letI := base_hasPushout F hKernelClosure a b f
  pushout.inr _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The square
with upper span κK,T_b(f) and lower legs u,v is the selected pushout square. -/
theorem base_isPushout (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    IsPushout ((kernelInclusion F hKernelClosure a b).app K)
      ((fullTruncationFunctor F hKernelClosure a b).map f)
      (baseInOld F hKernelClosure a b f) (baseInKernel F hKernelClosure a b f) := by
  let _ := base_hasPushout F hKernelClosure a b f
  exact IsPushout.of_hasPushout _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. Naturality
induces c:P_f→L, with u≫c=f and v≫c=κL. -/
def baseCorner (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    base F hKernelClosure a b f ⟶ L :=
  letI := base_hasPushout F hKernelClosure a b f
  pushout.desc f ((kernelInclusion F hKernelClosure a b).app L)
    ((kernelInclusion F hKernelClosure a b).naturality f).symm

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The induced
corner c:P_f→L satisfies u≫c=f. -/
theorem baseInOld_corner (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseInOld F hKernelClosure a b f ≫ baseCorner F hKernelClosure a b f = f := by
  let _ := base_hasPushout F hKernelClosure a b f
  exact pushout.inl_desc _ _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The induced
corner c:P_f→L satisfies v≫c=κL. -/
theorem baseInKernel_corner (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseInKernel F hKernelClosure a b f ≫ baseCorner F hKernelClosure a b f =
      (kernelInclusion F hKernelClosure a b).app L := by
  let _ := base_hasPushout F hKernelClosure a b f
  exact pushout.inr_desc _ _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The maps
πK:K→D_b(K) and zero on T_b(L) extend to q:P_f→D_b(K). -/
def baseQuotient (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    base F hKernelClosure a b f ⟶ (diskFunctor F a b).obj K :=
  letI := base_hasPushout F hKernelClosure a b f
  pushout.desc ((diskProjection F a b).app K) 0 (by
    rw [kernelInclusion_projection, comp_zero])

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
quotient q:P_f→D_b(K) satisfies u≫q=πK. -/
theorem baseInOld_quotient (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseInOld F hKernelClosure a b f ≫ baseQuotient F hKernelClosure a b f =
      (diskProjection F a b).app K := by
  let _ := base_hasPushout F hKernelClosure a b f
  exact pushout.inl_desc _ _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
quotient q:P_f→D_b(K) satisfies v≫q=0. -/
theorem baseInKernel_quotient (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseInKernel F hKernelClosure a b f ≫ baseQuotient F hKernelClosure a b f = 0 := by
  let _ := base_hasPushout F hKernelClosure a b f
  exact pushout.inr_desc _ _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
new-kernel leg and quotient form the short complex T_b(L)→P_f→D_b(K). -/
abbrev baseRow (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    ShortComplex (AmbientAcyclicWindow F a b) :=
  ShortComplex.mk (baseInKernel F hKernelClosure a b f) (baseQuotient F hKernelClosure a b f)
    (baseInKernel_quotient F hKernelClosure a b f)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. Evaluate
the conormal row in degree p to obtain T_b(L)ᵖ→P_fᵖ→D_b(K)ᵖ in E. -/
abbrev baseTermRow (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) (p : ℤ) :
    ShortComplex E :=
  (baseRow F hKernelClosure a b f).map
    (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. Every
degree-p conormal row T_b(L)ᵖ→P_fᵖ→D_b(K)ᵖ is admissible exact, as the cobase change of the
original kernel row. -/
theorem baseTermRow_isAdmissibleExact (a b : ℤ) {K L : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) (p : ℤ) : IsAdmissibleExact (baseTermRow F hKernelClosure a b f p) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let i := (kernelInclusion F hKernelClosure a b).app K
  let u := (fullTruncationFunctor F hKernelClosure a b).map f
  let x := baseInOld F hKernelClosure a b f
  let y := baseInKernel F hKernelClosure a b f
  let q := baseQuotient F hKernelClosure a b f
  let π := (diskProjection F a b).app K
  have hP := ambientAcyclicWindowPushout_term F a b (i := i) (f := u) (inY := x) (inZ := y)
    ((ambientAcyclicWindow_isCofibration_iff F a b i).mp
      (kernelInclusion_isCofibration F hKernelClosure a b K))
    (base_isPushout F hKernelClosure a b f) p
  let w : i.hom.hom.hom.f p ≫ π.hom.hom.hom.f p = 0 :=
    (shortKernelTerm F hKernelClosure a b K p).zero
  let q₀ := pushoutQuotientMap (u.hom.hom.hom.f p) (i.hom.hom.hom.f p)
    (π.hom.hom.hom.f p) (y.hom.hom.hom.f p) (x.hom.hom.hom.f p) w hP.flip
  have hx₀ : x.hom.hom.hom.f p ≫ q₀ = π.hom.hom.hom.f p :=
    pushoutQuotientMap_y _ _ _ _ _ _ _
  have hy₀ : y.hom.hom.hom.f p ≫ q₀ = 0 := pushoutQuotientMap_x _ _ _ _ _ _ _
  have hx : x.hom.hom.hom.f p ≫ q.hom.hom.hom.f p = π.hom.hom.hom.f p :=
    congrArg (fun z => z.hom.hom.hom.f p) (baseInOld_quotient F hKernelClosure a b f)
  have hy : y.hom.hom.hom.f p ≫ q.hom.hom.hom.f p = 0 :=
    congrArg (fun z => z.hom.hom.hom.f p) (baseInKernel_quotient F hKernelClosure a b f)
  have hq : q₀ = q.hom.hom.hom.f p := hP.hom_ext (hx₀.trans hx.symm) (hy₀.trans hy.symm)
  have hRow : IsAdmissibleExact (ShortComplex.mk (y.hom.hom.hom.f p) q₀ hy₀) :=
    isAdmissibleExact_pushoutQuotientMap (u.hom.hom.hom.f p) (i.hom.hom.hom.f p)
      (π.hom.hom.hom.f p) (y.hom.hom.hom.f p) (x.hom.hom.hom.f p) w
      (shortKernelTerm_isAdmissibleExact F hKernelClosure a b K p) hP.flip
  change IsAdmissibleExact
    (ShortComplex.mk (y.hom.hom.hom.f p) (q.hom.hom.hom.f p) _)
  simpa only [hq] using hRow

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The corner
c and quotient q satisfy c≫πL=q≫D_b(f). -/
theorem baseCorner_projection (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseCorner F hKernelClosure a b f ≫ (diskProjection F a b).app L =
      baseQuotient F hKernelClosure a b f ≫ (diskFunctor F a b).map f := by
  apply (base_isPushout F hKernelClosure a b f).hom_ext
  · rw [← Category.assoc, baseInOld_corner, ← Category.assoc, baseInOld_quotient]
    exact (diskProjection F a b).naturality f
  · rw [← Category.assoc, baseInKernel_corner, kernelInclusion_projection,
      ← Category.assoc, baseInKernel_quotient, zero_comp]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. The
identity of T_b(L), corner c and disk map D_b(f) define a morphism from the base conormal row to
the top-kernel row of L. -/
def baseConormal (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    baseRow F hKernelClosure a b f ⟶ shortKernel F hKernelClosure a b L :=
  ShortComplex.homMk (𝟙 _) (baseCorner F hKernelClosure a b f) ((diskFunctor F a b).map f)
    (by rw [Category.id_comp]; exact (baseInKernel_corner F hKernelClosure a b f).symm)
    (baseCorner_projection F hKernelClosure a b f)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. If f is a
window cofibration, every component of c:P_f→L is an admissible mono in E. -/
theorem baseCorner_isAdmissibleMono_f (a b : ℤ) {K L : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) (hf : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration f) (p : ℤ) :
    IsAdmissibleMono ((baseCorner F hKernelClosure a b f).hom.hom.hom.f p) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let G := ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p
  let φ := G.mapShortComplex.map (baseConormal F hKernelClosure a b f)
  let _ : IsIso φ.τ₁ := by
    change IsIso (G.map (𝟙 _))
    rw [G.map_id]
    infer_instance
  have hDisk : IsCofibration ((diskFunctor F a b).map f) :=
    (diskFunctor_isWaldhausenExact F a b).map_cofibration f hf
  exact isAdmissibleMono_middle_of_isIso_left φ
    (baseTermRow_isAdmissibleExact F hKernelClosure a b f p)
    (shortKernelTerm_isAdmissibleExact F hKernelClosure a b L p)
    ((ambientAcyclicWindow_isCofibration_iff F a b _).mp hDisk p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. For a window map
f:K→L, let P_f=K⊔_(T_b K)T_b L, with old leg u:K→P_f and new-kernel leg v:T_b L→P_f. If f is a
window cofibration, then the induced corner c:P_f→L is also a window cofibration. -/
theorem baseCorner_isCofibration (a b : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsCofibration f → IsCofibration (baseCorner F hKernelClosure a b f) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  intro hf
  apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
  exact baseCorner_isAdmissibleMono_f F hKernelClosure a b f hf

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive, exact and fully faithful. Assume F reflects admissible exactness and its essential
image is closed under epi kernels between its objects. Use the F-acyclic [a,b] window with
componentwise admissible cofibrations and isomorphism weak maps. Write T_b for selected top
truncation, D_b(K)=Dᵇ(Kᵇ), and κ,π for their natural inclusion and projection. The exact
endofunctors T_b, identity and D_b, with κ and π, form a Waldhausen cofiber-functor sequence.
The objectwise cofibers and the relative base-corner cofibrations are those constructed above. -/
theorem cofiberFunctorSequence (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsWaldhausenCofiberFunctorSequence (fullTruncationFunctor F hKernelClosure a b)
      (Functor.id (AmbientAcyclicWindow F a b)) (diskFunctor F a b)
      (kernelInclusion F hKernelClosure a b) (diskProjection F a b) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  refine {
    sourceExact := fullTruncationFunctor_isWaldhausenExact F hKernelClosure a b
    middleExact := Functor.IsWaldhausenExact.id
    quotientExact := diskFunctor_isWaldhausenExact F a b
    objectwise := objectwise_cofiberSequence F hKernelClosure a b
    baseCofibration := ?_ }
  intro K L f hf
  exact baseCorner_isCofibration F hKernelClosure a b f hf

end CochainComplex.Bounded.AmbientWindowTruncation

end
