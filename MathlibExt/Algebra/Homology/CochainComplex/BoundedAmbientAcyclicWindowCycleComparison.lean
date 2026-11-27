/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindowTruncationSequence

/-!
# Selected source-cycle comparisons across support windows

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Suppose F reflects admissible exactness, and the kernel of every
epi between objects of its essential image also lies in that image. For F-acyclic supported
cochains, these hypotheses give selected cycle objects in E representing outgoing differential
kernels.

Raw cochain maps between different windows lift to maps of these cycles, characterized by the
inclusion square. They preserve identity and composition, so raw isomorphisms and natural charts
induce cycle isomorphisms. The lower-boundary cycle is zero, the upper-boundary cycle is the top
term, and an identity disk has its source as the upper cycle and zero cycles elsewhere.

With F exact, top truncation preserves every degree-p cycle for p≠b. The shorter-window and
same-window descriptions compare through their common raw kernel. E and A retain independent
object and Hom universes; natural charts may be indexed by a further independently sized
category B.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientWindowCycleComparison

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For F-acyclic K,L in any two
support windows and a raw cochain map f:K→L, the composite ιK≫fᵖ≫dLᵖ is zero. -/
theorem inclusion_rawMap_d (a b c d p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (f : K.obj.obj.obj ⟶ L.obj.obj.obj) :
    ((AmbientWindowCycles.data F hKernelClosure a b p K).ι ≫ f.f p) ≫
      L.obj.obj.obj.d p (p + 1) = 0 := by
  rw [Category.assoc, f.comm p (p + 1), ← Category.assoc,
    (AmbientWindowCycles.data F hKernelClosure a b p K).zero, zero_comp]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. A raw cochain map f:K→L
between F-acyclic objects in any two windows induces Zᵖ(f):Zᵖ(K)→Zᵖ(L), characterized by
Zᵖ(f)≫ιL=ιK≫fᵖ. -/
def mapOfRaw (a b c d p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (f : K.obj.obj.obj ⟶ L.obj.obj.obj) :
    (AmbientWindowCycles.functor F hKernelClosure a b p).obj K ⟶
      (AmbientWindowCycles.functor F hKernelClosure c d p).obj L :=
  (KernelFork.IsLimit.lift' (AmbientWindowCycles.kernelIsLimit F hKernelClosure c d p L)
    ((AmbientWindowCycles.data F hKernelClosure a b p K).ι ≫ f.f p)
    (inclusion_rawMap_d F hKernelClosure a b c d p K L f)).1

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a raw map f:K→L between
F-acyclic window complexes, the induced cycle map satisfies Zᵖ(f)≫ιL=ιK≫fᵖ. -/
theorem mapOfRaw_ι (a b c d p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (f : K.obj.obj.obj ⟶ L.obj.obj.obj) :
    mapOfRaw F hKernelClosure a b c d p K L f ≫
        (AmbientWindowCycles.data F hKernelClosure c d p L).ι =
      (AmbientWindowCycles.data F hKernelClosure a b p K).ι ≫ f.f p :=
  (KernelFork.IsLimit.lift' (AmbientWindowCycles.kernelIsLimit F hKernelClosure c d p L)
    ((AmbientWindowCycles.data F hKernelClosure a b p K).ι ≫ f.f p)
    (inclusion_rawMap_d F hKernelClosure a b c d p K L f)).2

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For each F-acyclic window
complex K, the selected cycle lift of the raw identity of K is the identity of Zᵖ(K). -/
theorem mapOfRaw_id (a b p : ℤ) (K : AmbientAcyclicWindow F a b) :
    mapOfRaw F hKernelClosure a b a b p K K (𝟙 K.obj.obj.obj) =
      𝟙 ((AmbientWindowCycles.functor F hKernelClosure a b p).obj K) := by
  let _ : Mono (AmbientWindowCycles.data F hKernelClosure a b p K).ι :=
    Fork.IsLimit.mono (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b p K)
  apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure a b p K).ι).mp
  simpa only [HomologicalComplex.id_f, Category.comp_id, Category.id_comp] using
    mapOfRaw_ι F hKernelClosure a b a b p K K (𝟙 K.obj.obj.obj)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For raw cochain maps f:K→L
and g:L→M between three F-acyclic support windows, Zᵖ(f≫g)=Zᵖ(f)≫Zᵖ(g). -/
theorem mapOfRaw_comp (a b c d e g p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (M : AmbientAcyclicWindow F e g)
    (f : K.obj.obj.obj ⟶ L.obj.obj.obj) (h : L.obj.obj.obj ⟶ M.obj.obj.obj) :
    mapOfRaw F hKernelClosure a b e g p K M (f ≫ h) =
      mapOfRaw F hKernelClosure a b c d p K L f ≫
        mapOfRaw F hKernelClosure c d e g p L M h := by
  let _ : Mono (AmbientWindowCycles.data F hKernelClosure e g p M).ι :=
    Fork.IsLimit.mono (AmbientWindowCycles.kernelIsLimit F hKernelClosure e g p M)
  apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure e g p M).ι).mp
  rw [mapOfRaw_ι, Category.assoc, mapOfRaw_ι, ← Category.assoc, mapOfRaw_ι,
    HomologicalComplex.comp_f, Category.assoc]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. If K,L belong to the same
support window and f is a morphism of its acyclic full category, the cross-window raw lift is
the cycle-functor map of f. -/
theorem mapOfRaw_ambientMap (a b p : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    mapOfRaw F hKernelClosure a b a b p K L f.hom.hom.hom =
      AmbientWindowCycles.map F hKernelClosure a b p f := by
  let _ : Mono (AmbientWindowCycles.data F hKernelClosure a b p L).ι :=
    Fork.IsLimit.mono (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b p L)
  apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure a b p L).ι).mp
  rw [mapOfRaw_ι, AmbientWindowCycles.map_ι]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. A raw cochain isomorphism
e:K≅L between F-acyclic objects in any two windows induces Zᵖ(K)≅Zᵖ(L), with maps given by the
cycle lifts of e and its inverse. -/
def isoOfRawIso (a b c d p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (e : K.obj.obj.obj ≅ L.obj.obj.obj) :
    (AmbientWindowCycles.functor F hKernelClosure a b p).obj K ≅
      (AmbientWindowCycles.functor F hKernelClosure c d p).obj L where
  hom := mapOfRaw F hKernelClosure a b c d p K L e.hom
  inv := mapOfRaw F hKernelClosure c d a b p L K e.inv
  hom_inv_id := by rw [← mapOfRaw_comp, e.hom_inv_id, mapOfRaw_id]
  inv_hom_id := by rw [← mapOfRaw_comp, e.inv_hom_id, mapOfRaw_id]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. The forward cycle chart of a
raw isomorphism e:K≅L satisfies Zᵖ(e)≫ιL=ιK≫eᵖ. -/
theorem isoOfRawIso_hom_ι (a b c d p : ℤ)
    (K : AmbientAcyclicWindow F a b) (L : AmbientAcyclicWindow F c d)
    (e : K.obj.obj.obj ≅ L.obj.obj.obj) :
    (isoOfRawIso F hKernelClosure a b c d p K L e).hom ≫
        (AmbientWindowCycles.data F hKernelClosure c d p L).ι =
      (AmbientWindowCycles.data F hKernelClosure a b p K).ι ≫ e.hom.f p :=
  mapOfRaw_ι F hKernelClosure a b c d p K L e.hom

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Let T and U be diagrams over
any category B with values in two F-acyclic support-window categories. A natural isomorphism of
their underlying raw cochain diagrams induces a natural isomorphism of their selected degree-p
E-cycles. -/
def natIsoOfRawNatIso {B : Type uB} [Category.{vB} B] (a b c d p : ℤ)
    (T : B ⥤ AmbientAcyclicWindow F a b) (U : B ⥤ AmbientAcyclicWindow F c d)
    (e : T ⋙ ambientAcyclicWindowRaw F a b ≅ U ⋙ ambientAcyclicWindowRaw F c d) :
    T ⋙ AmbientWindowCycles.functor F hKernelClosure a b p ≅
      U ⋙ AmbientWindowCycles.functor F hKernelClosure c d p :=
  NatIso.ofComponents
    (fun X => isoOfRawIso F hKernelClosure a b c d p (T.obj X) (U.obj X) (e.app X))
    (fun {X Y} f => by
      let _ : Mono (AmbientWindowCycles.data F hKernelClosure c d p (U.obj Y)).ι :=
        Fork.IsLimit.mono
          (AmbientWindowCycles.kernelIsLimit F hKernelClosure c d p (U.obj Y))
      apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure c d p (U.obj Y)).ι).mp
      have hn := congrArg (fun h => h.f p) (e.hom.naturality f)
      change (T.map f).hom.hom.hom.f p ≫ (e.app Y).hom.f p =
        (e.app X).hom.f p ≫ (U.map f).hom.hom.hom.f p at hn
      change (AmbientWindowCycles.map F hKernelClosure a b p (T.map f) ≫
          mapOfRaw F hKernelClosure a b c d p (T.obj Y) (U.obj Y) (e.app Y).hom) ≫ _ =
        (mapOfRaw F hKernelClosure a b c d p (T.obj X) (U.obj X) (e.app X).hom ≫
          AmbientWindowCycles.map F hKernelClosure c d p (U.map f)) ≫ _
      rw [Category.assoc, mapOfRaw_ι, ← Category.assoc, AmbientWindowCycles.map_ι,
        Category.assoc, hn, ← Category.assoc, ← mapOfRaw_ι]
      simpa only [Category.assoc] using (congrArg
        (fun z => mapOfRaw F hKernelClosure a b c d p (T.obj X) (U.obj X) (e.app X).hom ≫ z)
        (AmbientWindowCycles.map_ι F hKernelClosure c d p (U.map f))).symm)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. If the term
Kᵖ is zero, its selected cycle object Zᵖ(K) is zero. -/
theorem isZero_of_term (a b p : ℤ) (K : AmbientAcyclicWindow F a b)
    (hTerm : IsZero (K.obj.obj.obj.X p)) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b p).obj K) := by
  let _ : Mono (AmbientWindowCycles.data F hKernelClosure a b p K).ι :=
    Fork.IsLimit.mono (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b p K)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (AmbientWindowCycles.data F hKernelClosure a b p K).ι).mp
  simp only [Category.id_comp, zero_comp]
  exact hTerm.eq_of_tgt _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. If the
preceding term Kᵖ⁻¹ is zero, acyclicity makes the incoming quotient onto Zᵖ(K) zero, so Zᵖ(K) is
zero. -/
theorem isZero_of_prev (a b p : ℤ) (K : AmbientAcyclicWindow F a b)
    (hPrev : IsZero (K.obj.obj.obj.X (p - 1))) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b p).obj K) := by
  let D := AmbientWindowCycles.data F hKernelClosure a b p K
  let _ : Epi (F.map D.q) := D.mappedEpi
  have hSource : IsZero (F.obj (K.obj.obj.obj.X (p - 1))) := F.map_isZero hPrev
  have hTarget : IsZero (F.obj D.Z) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_epi (F.map D.q)).mp
    simp only [Category.comp_id, comp_zero]
    exact hSource.eq_of_src _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact hTarget.eq_of_src _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The lower
boundary cycle Zᵃ(K) is zero because Kᵃ⁻¹ is outside the support. -/
theorem left_isZero (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b a).obj K) :=
  isZero_of_prev F hKernelClosure a b a K (K.obj.property (a - 1) (Or.inl (by omega)))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The top cycle
inclusion ι:Zᵇ(K)→Kᵇ is an isomorphism, since the next term Kᵇ⁺¹ is zero. -/
theorem top_ι_isIso (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsIso (AmbientWindowCycles.data F hKernelClosure a b b K).ι := by
  have hd : K.obj.obj.obj.d b (b + 1) = 0 :=
    (K.obj.property (b + 1) (Or.inr (by omega))).eq_of_tgt _ _
  exact KernelFork.IsLimit.isIso_ι _
    (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b b K) hd

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The inclusion
ι gives the selected top-cycle chart Zᵇ(K)≅Kᵇ. -/
def topIso (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    (AmbientWindowCycles.functor F hKernelClosure a b b).obj K ≅ K.obj.obj.obj.X b := by
  let _ := top_ι_isIso F hKernelClosure a b K
  exact asIso (AmbientWindowCycles.data F hKernelClosure a b b K).ι

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The charts
Zᵇ(K)≅Kᵇ are natural in all cochain maps of the fixed F-acyclic window. -/
def topNatIso (a b : ℤ) :
    AmbientWindowCycles.functor F hKernelClosure a b b ≅
      ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) b :=
  NatIso.ofComponents (topIso F hKernelClosure a b)
    (fun {_K _L} f => AmbientWindowCycles.map_ι F hKernelClosure a b b f)

omit [ExactCategory E] in
/-- Let E be preadditive with zero and binary biproducts. For the identity disk Dʲ(X), the
differential from degree j−1 to j is an isomorphism. Its lower and upper term charts identify it
with the positive identity of X. -/
theorem signedDisk_d_isIso (j : ℤ) (X : E) :
    IsIso (((SignedDisk.raw E j).obj X).d (j - 1) j) := by
  have hd : ((SignedDisk.raw E j).obj X).d (j - 1) j =
      (SignedDisk.lowerIso E j X).inv ≫ (SignedDisk.upperIso E j X).hom := by
    apply (cancel_epi (SignedDisk.lowerIso E j X).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using SignedDisk.lowerIso_hom_d E j X
  rw [hd]
  infer_instance

private theorem isZero_of_sameRawDisk (a b j p : ℤ)
    (K : AmbientAcyclicWindow F a b) (X : E)
    (hRaw : K.obj.obj.obj = (SignedDisk.raw E j).obj X) (hp : p ≠ j) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b p).obj K) := by
  by_cases hLower : p = j - 1
  · subst p
    let _ : IsIso (K.obj.obj.obj.d (j - 1) (j - 1 + 1)) := by
      rw [show j - 1 + 1 = j by omega, hRaw]
      exact signedDisk_d_isIso j X
    exact KernelFork.IsLimit.isZero_of_mono
      (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b (j - 1) K)
  apply isZero_of_term F hKernelClosure a b p K
  rw [hRaw]
  exact SignedDisk.isZero_X E j X p hLower hp

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, the
supported identity disk Dʲ(X) has zero selected cycle Zᵖ whenever p≠j. -/
theorem signedDisk_isZero_off (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b)
    (X : E) (p : ℤ) (hp : p ≠ j) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b p).obj
      ((SignedDisk.ambient E F a b j ha hb).obj X)) :=
  isZero_of_sameRawDisk F hKernelClosure a b j p
    ((SignedDisk.ambient E F a b j ha hb).obj X) X rfl hp

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The top-disk
endofunctor Dᵇ(Kᵇ) has zero degree-p source cycles whenever p≠b, for every support window. -/
theorem diskFunctor_isZero_off (a b : ℤ) (K : AmbientAcyclicWindow F a b)
    (p : ℤ) (hp : p ≠ b) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b p).obj
      ((AmbientWindowTruncation.diskFunctor F a b).obj K)) :=
  isZero_of_sameRawDisk F hKernelClosure a b b p
    ((AmbientWindowTruncation.diskFunctor F a b).obj K) (K.obj.obj.obj.X b) rfl hp

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, the
selected cycle inclusion of the supported identity disk Dʲ(X) in degree j is an isomorphism onto
its upper term. -/
theorem signedDisk_ι_isIso (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) (X : E) :
    IsIso (AmbientWindowCycles.data F hKernelClosure a b j
      ((SignedDisk.ambient E F a b j ha hb).obj X)).ι := by
  have hd : ((SignedDisk.raw E j).obj X).d j (j + 1) = 0 :=
    (SignedDisk.isZero_X E j X (j + 1) (by omega) (by omega)).eq_of_tgt _ _
  exact KernelFork.IsLimit.isIso_ι _
    (AmbientWindowCycles.kernelIsLimit F hKernelClosure a b j
      ((SignedDisk.ambient E F a b j ha hb).obj X)) hd

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be preadditive with zero and binary biproducts. Let A be abelian and F:E→A additive. For
a≤j−1 and j≤b, the upper term of the ambient identity disk Dʲ(X) has the canonical chart
X≅Dʲ(X)ʲ. -/
def signedDiskUpperChart (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) (X : E) :
    X ≅ ((SignedDisk.ambient E F a b j ha hb).obj X).obj.obj.obj.X j :=
  SignedDisk.upperIso E j X

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be preadditive with zero and binary biproducts. Let A be abelian and F:E→A additive. For
a≤j−1 and j≤b, the upper-term charts are natural: the chart for X followed by the degree-j disk
component of f:X→Y equals f followed by the chart for Y. -/
theorem signedDiskUpperChart_naturality (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b)
    {X Y : E} (f : X ⟶ Y) :
    (signedDiskUpperChart F a b j ha hb X).hom ≫
        ((SignedDisk.ambient E F a b j ha hb).map f).hom.hom.hom.f j =
      f ≫ (signedDiskUpperChart F a b j ha hb Y).hom :=
  SignedDisk.upperIso_naturality E j f

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, compose
the selected cycle inclusion with the upper-term chart to identify Zʲ(Dʲ(X))≅X. -/
def signedDiskIso (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) (X : E) :
    (AmbientWindowCycles.functor F hKernelClosure a b j).obj
      ((SignedDisk.ambient E F a b j ha hb).obj X) ≅ X := by
  let _ := signedDisk_ι_isIso F hKernelClosure a b j ha hb X
  exact asIso (AmbientWindowCycles.data F hKernelClosure a b j
    ((SignedDisk.ambient E F a b j ha hb).obj X)).ι ≪≫
      (signedDiskUpperChart F a b j ha hb X).symm

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, the
forward chart Zʲ(Dʲ(X))→X followed by the upper-term chart X→Dʲ(X)ʲ is the selected cycle
inclusion. -/
theorem signedDiskIso_hom_ι (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) (X : E) :
    (signedDiskIso F hKernelClosure a b j ha hb X).hom ≫
        (signedDiskUpperChart F a b j ha hb X).hom =
      (AmbientWindowCycles.data F hKernelClosure a b j
        ((SignedDisk.ambient E F a b j ha hb).obj X)).ι := by
  change ((AmbientWindowCycles.data F hKernelClosure a b j
    ((SignedDisk.ambient E F a b j ha hb).obj X)).ι ≫
      (signedDiskUpperChart F a b j ha hb X).inv) ≫
        (signedDiskUpperChart F a b j ha hb X).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, the
inverse chart X→Zʲ(Dʲ(X)) followed by the cycle inclusion is the upper-term chart. -/
theorem signedDiskIso_inv_ι (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) (X : E) :
    (signedDiskIso F hKernelClosure a b j ha hb X).inv ≫
        (AmbientWindowCycles.data F hKernelClosure a b j
          ((SignedDisk.ambient E F a b j ha hb).obj X)).ι =
      (signedDiskUpperChart F a b j ha hb X).hom := by
  rw [← signedDiskIso_hom_ι, Iso.inv_hom_id_assoc]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a≤j−1 and j≤b, the
supported identity-disk functor followed by degree-j source cycles is naturally isomorphic to
the identity functor of E. -/
def signedDiskNatIso (a b j : ℤ) (ha : a ≤ j - 1) (hb : j ≤ b) :
    SignedDisk.ambient E F a b j ha hb ⋙ AmbientWindowCycles.functor F hKernelClosure a b j ≅
      Functor.id E :=
  NatIso.ofComponents (signedDiskIso F hKernelClosure a b j ha hb) (fun {X Y} f => by
    apply (cancel_mono (signedDiskUpperChart F a b j ha hb Y).hom).mp
    change (AmbientWindowCycles.map F hKernelClosure a b j
        ((SignedDisk.ambient E F a b j ha hb).map f) ≫
          (signedDiskIso F hKernelClosure a b j ha hb Y).hom) ≫ _ =
      ((signedDiskIso F hKernelClosure a b j ha hb X).hom ≫ f) ≫ _
    rw [Category.assoc, signedDiskIso_hom_ι, AmbientWindowCycles.map_ι,
      Category.assoc, ← signedDiskUpperChart_naturality, ← Category.assoc,
      signedDiskIso_hom_ι])

variable [F.IsExact]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. Assume F is
exact. For every p≠b, the selected cycle map of the top-truncation inclusion T_b(K)→K is an
isomorphism. -/
theorem truncationCycleMap_isIso (a b p : ℤ) (hp : p ≠ b) (K : AmbientAcyclicWindow F a b) :
    IsIso (AmbientWindowCycles.map F hKernelClosure a b p
      ((AmbientWindowTruncation.kernelInclusion F hKernelClosure a b).app K)) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let S := AmbientWindowTruncation.shortKernel F hKernelClosure a b K
  let T := AmbientWindowCycles.row F hKernelClosure a b p S
  have hT : IsAdmissibleExact T :=
    AmbientWindowCycles.row_isAdmissibleExact_of_isCofibrationSequence F hKernelClosure a b p S
      (AmbientWindowTruncation.objectwise_cofiberSequence F hKernelClosure a b K)
  have hg : T.g = 0 := (diskFunctor_isZero_off F hKernelClosure a b K p hp).eq_of_tgt _ _
  exact KernelFork.IsLimit.isIso_ι _ (isLimit_kernelFork_of_isAdmissibleExact hT) hg

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. Assume F is
exact. For p≠b, the cycle maps of T_b(K)→K form a natural isomorphism from degree-p cycles after
same-window truncation to the original degree-p cycle functor. -/
def truncationCycleNatIso (a b p : ℤ) (hp : p ≠ b) :
    AmbientWindowTruncation.fullTruncationFunctor F hKernelClosure a b ⋙
      AmbientWindowCycles.functor F hKernelClosure a b p ≅
        AmbientWindowCycles.functor F hKernelClosure a b p :=
  NatIso.ofComponents
    (fun K =>
      letI := truncationCycleMap_isIso F hKernelClosure a b p hp K
      asIso (AmbientWindowCycles.map F hKernelClosure a b p
        ((AmbientWindowTruncation.kernelInclusion F hKernelClosure a b).app K)))
    (fun {_K _L} f => (Functor.whiskerRight
      (AmbientWindowTruncation.kernelInclusion F hKernelClosure a b)
      (AmbientWindowCycles.functor F hKernelClosure a b p)).naturality f)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. Assume F is
exact. Regard the same truncation kernel either in [a,b−1] or in [a,b]. Their underlying raw
complexes agree, giving a natural chart between the selected cycle functors in every degree p. -/
def shorterFullCycleNatIso (a b p : ℤ) :
    AmbientWindowTruncation.shorterFunctor F hKernelClosure a b ⋙
      AmbientWindowCycles.functor F hKernelClosure a (b - 1) p ≅
        AmbientWindowTruncation.fullTruncationFunctor F hKernelClosure a b ⋙
          AmbientWindowCycles.functor F hKernelClosure a b p :=
  natIsoOfRawNatIso F hKernelClosure a (b - 1) a b p
    (AmbientWindowTruncation.shorterFunctor F hKernelClosure a b)
    (AmbientWindowTruncation.fullTruncationFunctor F hKernelClosure a b) (eqToIso (by rfl))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. Assume F is
exact. For every p≠b, shorter-window truncation followed by degree-p cycles is naturally
isomorphic to the original degree-p cycle functor. -/
def shorterCycleNatIso (a b p : ℤ) (hp : p ≠ b) :
    AmbientWindowTruncation.shorterFunctor F hKernelClosure a b ⋙
      AmbientWindowCycles.functor F hKernelClosure a (b - 1) p ≅
        AmbientWindowCycles.functor F hKernelClosure a b p :=
  shorterFullCycleNatIso F hKernelClosure a b p ≪≫
    truncationCycleNatIso F hKernelClosure a b p hp

end CochainComplex.Bounded.AmbientWindowCycleComparison

end
