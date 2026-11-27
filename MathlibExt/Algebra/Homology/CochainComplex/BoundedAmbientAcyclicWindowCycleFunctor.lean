/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindow
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicCycles
public import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag
public import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Functorial source cycles of ambient-acyclic window complexes

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume that F reflects admissible exactness and its essential image
is closed under kernels of epimorphisms between its objects. An F-acyclic complex K supported in
[a,b] then has selected source cycles Zʲ(K) representing ker(dʲ).

Kernel lifts make Zʲ an additive functor. Its natural inclusion ι:Zʲ(K)→Kʲ and incoming quotient
q:Kʲ⁻¹→Zʲ(K) satisfy q≫ι=dʲ⁻¹. After F, cycle maps are monic from monicity in degree j and epic
from epicity in degree j−1. Componentwise short exact rows give short exact mapped cycle rows.

When F is exact, source conflations and admissible pushouts are preserved, making the cycle
functor Waldhausen exact in the specified isomorphism-weak models. The E and A object and Hom
universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientWindowCycles

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. These cycle
data include Zʲ(K), its inclusion into Kʲ and the incoming quotient Kʲ⁻¹→Zʲ(K), chosen from the
ambient-acyclic support data. -/
abbrev data (a b j : ℤ) (K : AmbientAcyclicWindow F a b) :
    AmbientCycles.CycleData F K.obj.obj j :=
  AmbientCycles.dataAt F K.obj.obj a b K.obj.property K.property hKernelClosure j

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The fork
Zʲ(K)→Kʲ with its inclusion is a kernel fork for the outgoing differential dʲ:Kʲ→Kʲ⁺¹. -/
def kernelIsLimit (a b j : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsLimit (KernelFork.ofι (f := K.obj.obj.obj.d j (j + 1))
      (data F hKernelClosure a b j K).ι (data F hKernelClosure a b j K).zero) := by
  let _ : Mono (data F hKernelClosure a b (j + 1) K).ι :=
    AmbientCycles.inclusion_mono F K.obj.obj a b K.obj.property K.property hKernelClosure (j + 1)
  exact isKernelCompMono
    (AmbientCycles.rowIsLimit F K.obj.obj a b K.obj.property K.property hKernelClosure j)
    (data F hKernelClosure a b (j + 1) K).ι
    (AmbientCycles.outgoing_factor F K.obj.obj a b K.obj.property K.property hKernelClosure j).symm

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a map f:K→L in one
F-acyclic support window, ιK≫fʲ≫dLʲ=0, so its source cycle inclusion lands in the target kernel. -/
theorem inclusion_map_d (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    ((data F hKernelClosure a b j K).ι ≫ f.hom.hom.hom.f j) ≫
      L.obj.obj.obj.d j (j + 1) = 0 := by
  rw [Category.assoc, f.hom.hom.hom.comm j (j + 1), ← Category.assoc,
    (data F hKernelClosure a b j K).zero, zero_comp]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. A cochain map f:K→L in the
fixed F-acyclic window induces the unique source cycle map Zʲ(K)→Zʲ(L) whose composite with ιL
is ιK≫fʲ. -/
def map (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    (data F hKernelClosure a b j K).Z ⟶ (data F hKernelClosure a b j L).Z :=
  (KernelFork.IsLimit.lift' (kernelIsLimit F hKernelClosure a b j L)
    ((data F hKernelClosure a b j K).ι ≫ f.hom.hom.hom.f j)
    (inclusion_map_d F hKernelClosure a b j f)).1

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a map f:K→L of F-acyclic
window complexes, Zʲ(f)≫ιL=ιK≫fʲ. -/
theorem map_ι (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    map F hKernelClosure a b j f ≫ (data F hKernelClosure a b j L).ι =
      (data F hKernelClosure a b j K).ι ≫ f.hom.hom.hom.f j :=
  (KernelFork.IsLimit.lift' (kernelIsLimit F hKernelClosure a b j L)
    ((data F hKernelClosure a b j K).ι ≫ f.hom.hom.hom.f j)
    (inclusion_map_d F hKernelClosure a b j f)).2

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The source
cycle map of id_K is id_(Zʲ(K)). -/
theorem map_id (a b j : ℤ) (K : AmbientAcyclicWindow F a b) :
    map F hKernelClosure a b j (𝟙 K) = 𝟙 (data F hKernelClosure a b j K).Z := by
  let _ : Mono (data F hKernelClosure a b j K).ι :=
    Fork.IsLimit.mono (kernelIsLimit F hKernelClosure a b j K)
  apply (cancel_mono (data F hKernelClosure a b j K).ι).mp
  have h := map_ι F hKernelClosure a b j (𝟙 K)
  have hid : (𝟙 K : K ⟶ K).hom.hom.hom.f j = 𝟙 (K.obj.obj.obj.X j) := rfl
  simpa only [hid, Category.comp_id, Category.id_comp] using h

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For window cochain maps f:K→L
and g:L→M, Zʲ(f≫g)=Zʲ(f)≫Zʲ(g). -/
theorem map_comp (a b j : ℤ) {K L M : AmbientAcyclicWindow F a b}
    (f : K ⟶ L) (g : L ⟶ M) :
    map F hKernelClosure a b j (f ≫ g) =
      map F hKernelClosure a b j f ≫ map F hKernelClosure a b j g := by
  let _ : Mono (data F hKernelClosure a b j M).ι :=
    Fork.IsLimit.mono (kernelIsLimit F hKernelClosure a b j M)
  apply (cancel_mono (data F hKernelClosure a b j M).ι).mp
  rw [map_ι, Category.assoc, map_ι, ← Category.assoc, map_ι, Category.assoc]
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For maps f,g:K→L in the fixed
F-acyclic window, Zʲ(f+g)=Zʲ(f)+Zʲ(g). -/
theorem map_add (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f g : K ⟶ L) :
    map F hKernelClosure a b j (f + g) =
      map F hKernelClosure a b j f + map F hKernelClosure a b j g := by
  let _ : Mono (data F hKernelClosure a b j L).ι :=
    Fork.IsLimit.mono (kernelIsLimit F hKernelClosure a b j L)
  apply (cancel_mono (data F hKernelClosure a b j L).ι).mp
  rw [Preadditive.add_comp, map_ι, map_ι, map_ι]
  change (data F hKernelClosure a b j K).ι ≫
      (f.hom.hom.hom.f j + g.hom.hom.hom.f j) =
    (data F hKernelClosure a b j K).ι ≫ f.hom.hom.hom.f j +
      (data F hKernelClosure a b j K).ι ≫ g.hom.hom.hom.f j
  exact Preadditive.comp_add (data F hKernelClosure a b j K).Z
    (K.obj.obj.obj.X j) (L.obj.obj.obj.X j) (data F hKernelClosure a b j K).ι
    (f.hom.hom.hom.f j) (g.hom.hom.hom.f j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Taking the selected degree-j
source cycle of each F-acyclic [a,b]-supported complex, and the induced kernel maps, defines a
functor to E. -/
abbrev functor (a b j : ℤ) : AmbientAcyclicWindow F a b ⥤ E where
  obj K := (data F hKernelClosure a b j K).Z
  map f := map F hKernelClosure a b j f
  map_id K := map_id F hKernelClosure a b j K
  map_comp f g := map_comp F hKernelClosure a b j f g

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. The degree-j source cycle
functor on the F-acyclic [a,b] window is additive. -/
instance functor_additive (a b j : ℤ) : (functor F hKernelClosure a b j).Additive where
  map_add {X Y} f g := by exact map_add F hKernelClosure a b j f g

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The cycle
inclusions ιK:Zʲ(K)→Kʲ form a natural transformation from the cycle functor to raw degree-j
evaluation. -/
def inclusion (a b j : ℤ) : functor F hKernelClosure a b j ⟶
    ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) j where
  app K := (data F hKernelClosure a b j K).ι
  naturality {_K _L} f := map_ι F hKernelClosure a b j f

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For f:K→L, the incoming
quotients satisfy fʲ⁻¹≫qL=qK≫Zʲ(f), where qK:Kʲ⁻¹→Zʲ(K). -/
theorem quotient_naturality (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    f.hom.hom.hom.f (j - 1) ≫ (data F hKernelClosure a b j L).q =
      (data F hKernelClosure a b j K).q ≫ map F hKernelClosure a b j f := by
  let _ : Mono (data F hKernelClosure a b j L).ι :=
    Fork.IsLimit.mono (kernelIsLimit F hKernelClosure a b j L)
  apply (cancel_mono (data F hKernelClosure a b j L).ι).mp
  rw [Category.assoc, (data F hKernelClosure a b j L).factor,
    Category.assoc, map_ι, ← Category.assoc, (data F hKernelClosure a b j K).factor]
  exact f.hom.hom.hom.comm (j - 1) j

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The maps
qK:Kʲ⁻¹→Zʲ(K) form a natural transformation from raw preceding-degree evaluation to the cycle
functor. -/
def quotient (a b j : ℤ) :
    ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) (j - 1) ⟶
      functor F hKernelClosure a b j where
  app K := (data F hKernelClosure a b j K).q
  naturality {_K _L} f := quotient_naturality F hKernelClosure a b j f

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The incoming
quotient and cycle inclusion factor the differential: qK≫ιK=dKʲ⁻¹. -/
theorem quotient_inclusion (a b j : ℤ) (K : AmbientAcyclicWindow F a b) :
    (quotient F hKernelClosure a b j).app K ≫ (inclusion F hKernelClosure a b j).app K =
      K.obj.obj.obj.d (j - 1) j := by
  change (data F hKernelClosure a b j K).q ≫ (data F hKernelClosure a b j K).ι = _
  exact (data F hKernelClosure a b j K).factor

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. The inclusion
of the selected source cycle remains monic after applying F. -/
theorem mapped_inclusion_mono (a b j : ℤ) (K : AmbientAcyclicWindow F a b) :
    Mono (F.map (data F hKernelClosure a b j K).ι) :=
  Fork.IsLimit.mono (data F hKernelClosure a b j K).mappedIsLimit

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a window map f:K→L, if
F(fʲ) is monic, then F(Zʲ(f)) is monic. -/
theorem mapped_map_mono (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L)
    [Mono (F.map (f.hom.hom.hom.f j))] : Mono (F.map (map F hKernelClosure a b j f)) := by
  let _ := mapped_inclusion_mono F hKernelClosure a b j K
  let _ := mapped_inclusion_mono F hKernelClosure a b j L
  have h : F.map (map F hKernelClosure a b j f) ≫ F.map (data F hKernelClosure a b j L).ι =
      F.map (data F hKernelClosure a b j K).ι ≫ F.map (f.hom.hom.hom.f j) := by
    rw [← F.map_comp, map_ι, F.map_comp]
  have hmono : Mono (F.map (map F hKernelClosure a b j f) ≫
      F.map (data F hKernelClosure a b j L).ι) := by
    rw [h]
    infer_instance
  let _ := hmono
  exact mono_of_mono (F.map (map F hKernelClosure a b j f))
    (F.map (data F hKernelClosure a b j L).ι)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a window map f:K→L, if
F(fʲ⁻¹) is epic, then F(Zʲ(f)) is epic. -/
theorem mapped_map_epi (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L)
    [Epi (F.map (f.hom.hom.hom.f (j - 1)))] :
    Epi (F.map (map F hKernelClosure a b j f)) := by
  let _ := (data F hKernelClosure a b j L).mappedEpi
  have h : F.map (data F hKernelClosure a b j K).q ≫ F.map (map F hKernelClosure a b j f) =
      F.map (f.hom.hom.hom.f (j - 1)) ≫ F.map (data F hKernelClosure a b j L).q := by
    rw [← F.map_comp, ← quotient_naturality, F.map_comp]
  have hepi : Epi (F.map (data F hKernelClosure a b j K).q ≫
      F.map (map F hKernelClosure a b j f)) := by
    rw [h]
    infer_instance
  let _ := hepi
  exact epi_of_epi (F.map (data F hKernelClosure a b j K).q)
    (F.map (map F hKernelClosure a b j f))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. If j<a or
b<j, the selected source cycle Zʲ(K) is zero. -/
theorem isZero_outside (a b j : ℤ) (K : AmbientAcyclicWindow F a b) (hj : j < a ∨ b < j) :
    IsZero ((functor F hKernelClosure a b j).obj K) :=
  AmbientCycles.cycles_isZero_outside F K.obj.obj a b K.obj.property K.property hKernelClosure j hj

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For an F-acyclic cochain K
supported in [a,b], write Zᵖ(K) for its selected E-kernel of dᵖ, with inclusion ι. If K is a
zero object of its acyclic window category, then Zʲ(K) is a zero object of E. -/
theorem map_isZero (a b j : ℤ) (K : AmbientAcyclicWindow F a b) (hK : IsZero K) :
    IsZero ((functor F hKernelClosure a b j).obj K) := by
  let _ : Mono (data F hKernelClosure a b j K).ι :=
    Fork.IsLimit.mono (kernelIsLimit F hKernelClosure a b j K)
  have hTerm : IsZero (K.obj.obj.obj.X j) :=
    (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) j).map_isZero hK
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (data F hKernelClosure a b j K).ι).mp
  simp only [Category.id_comp, zero_comp]
  exact hTerm.eq_of_tgt _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. The cycle of the selected
zero of the F-acyclic [a,b] window is canonically isomorphic to the selected zero of E. -/
def zeroIso (a b j : ℤ) :
    (functor F hKernelClosure a b j).obj (0 : AmbientAcyclicWindow F a b) ≅ (0 : E) :=
  (map_isZero F hKernelClosure a b j _ (isZero_zero _)).isoZero

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. For a short complex S in the
F-acyclic [a,b] window, evaluate its three raw complexes and two maps in degree p to obtain a
short complex in E. -/
abbrev termRow (a b : ℤ) (S : ShortComplex (AmbientAcyclicWindow F a b)) (p : ℤ) :
    ShortComplex E :=
  (S.map (ambientAcyclicWindowRaw F a b)).map (HomologicalComplex.eval E (.up ℤ) p)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Applying the degree-j source
cycle functor to a short complex S in the F-acyclic [a,b] window gives its cycle row in E. -/
abbrev row (a b j : ℤ) (S : ShortComplex (AmbientAcyclicWindow F a b)) : ShortComplex E :=
  S.map (functor F hKernelClosure a b j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Let S be a short complex of
F-acyclic window complexes, with every degree-p component row short exact after F. Then the
first map of the F-image of its degree-j cycle row is a kernel of the second map. -/
def rowMappedKernelIsLimit (a b j : ℤ) (S : ShortComplex (AmbientAcyclicWindow F a b))
    (hTerms : ∀ p : ℤ, ((termRow F a b S p).map F).ShortExact) :
    let T := (row F hKernelClosure a b j S).map F
    IsLimit (KernelFork.ofι T.f T.zero) := by
  let T := (row F hKernelClosure a b j S).map F
  let D₁ := data F hKernelClosure a b j S.X₁
  let D₂ := data F hKernelClosure a b j S.X₂
  let D₃ := data F hKernelClosure a b j S.X₃
  let _ : Mono (F.map (S.f.hom.hom.hom.f j)) := (hTerms j).mono_f
  let _ : Mono T.f := mapped_map_mono F hKernelClosure a b j S.f
  refine KernelFork.IsLimit.ofι' T.f T.zero ?_
  intro W φ hφ
  have hg : T.g ≫ F.map D₃.ι = F.map D₂.ι ≫ F.map (S.g.hom.hom.hom.f j) := by
    change F.map (map F hKernelClosure a b j S.g) ≫ F.map D₃.ι = _
    rw [← F.map_comp, map_ι, F.map_comp]
  have hw : (φ ≫ F.map D₂.ι) ≫ F.map (S.g.hom.hom.hom.f j) = 0 := by
    rw [Category.assoc, ← hg, ← Category.assoc, hφ, zero_comp]
  let l := KernelFork.IsLimit.lift' (hTerms j).fIsKernel (φ ≫ F.map D₂.ι) hw
  have hl : l.1 ≫ F.map (S.f.hom.hom.hom.f j) = φ ≫ F.map D₂.ι := l.2
  have hd : l.1 ≫ F.map (S.X₁.obj.obj.obj.d j (j + 1)) = 0 := by
    let _ : Mono (F.map (S.f.hom.hom.hom.f (j + 1))) := (hTerms (j + 1)).mono_f
    apply (cancel_mono (F.map (S.f.hom.hom.hom.f (j + 1)))).mp
    simp only [zero_comp]
    have hcomm : F.map (S.X₁.obj.obj.obj.d j (j + 1)) ≫
        F.map (S.f.hom.hom.hom.f (j + 1)) =
      F.map (S.f.hom.hom.hom.f j) ≫ F.map (S.X₂.obj.obj.obj.d j (j + 1)) := by
      simpa only [F.map_comp] using
        (congrArg F.map (S.f.hom.hom.hom.comm j (j + 1))).symm
    have hz : F.map D₂.ι ≫ F.map (S.X₂.obj.obj.obj.d j (j + 1)) = 0 := by
      rw [← F.map_comp, D₂.zero, F.map_zero]
    rw [Category.assoc, hcomm, ← Category.assoc, hl, Category.assoc, hz, comp_zero]
  let β := KernelFork.IsLimit.lift' D₁.mappedIsLimit l.1 hd
  have hβι : β.1 ≫ F.map D₁.ι = l.1 := β.2
  have hβ : β.1 ≫ T.f = φ := by
    let _ := mapped_inclusion_mono F hKernelClosure a b j S.X₂
    apply (cancel_mono (F.map D₂.ι)).mp
    have hf : T.f ≫ F.map D₂.ι = F.map D₁.ι ≫ F.map (S.f.hom.hom.hom.f j) := by
      change F.map (map F hKernelClosure a b j S.f) ≫ F.map D₂.ι = _
      rw [← F.map_comp, map_ι, F.map_comp]
    rw [Category.assoc, hf, ← Category.assoc, hβι, hl]
  exact ⟨β.1, hβ⟩

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. If every component row of a
short complex S of F-acyclic window complexes is short exact after F, then the degree-j
source-cycle row is short exact after F. -/
theorem row_map_shortExact (a b j : ℤ) (S : ShortComplex (AmbientAcyclicWindow F a b))
    (hTerms : ∀ p : ℤ, ((termRow F a b S p).map F).ShortExact) :
    ((row F hKernelClosure a b j S).map F).ShortExact := by
  let T := (row F hKernelClosure a b j S).map F
  let hKernel := rowMappedKernelIsLimit F hKernelClosure a b j S hTerms
  let _ : Epi (F.map (S.g.hom.hom.hom.f (j - 1))) := (hTerms (j - 1)).epi_g
  have hEpi : Epi T.g := mapped_map_epi F hKernelClosure a b j S.g
  have hExact : T.Exact := T.exact_of_f_is_kernel hKernel
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKernel) hEpi

variable [F.IsExact]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. If every
E-component row of S is an admissible exact sequence, then the degree-j source-cycle row is also
admissible exact. -/
theorem row_isAdmissibleExact (a b j : ℤ) (S : ShortComplex (AmbientAcyclicWindow F a b))
    (hTerms : ∀ p : ℤ, IsAdmissibleExact (termRow F a b S p)) :
    IsAdmissibleExact (row F hKernelClosure a b j S) :=
  F.reflects_admissibleExact _ (row_map_shortExact F hKernelClosure a b j S
    (fun p => F.map_admissibleExact _ (hTerms p)))

omit [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. A
cofibration sequence of F-acyclic window complexes, in the degreewise-admissible and
isomorphism-weak model, evaluates to an admissible exact sequence in E at every degree p. -/
theorem termRow_isAdmissibleExact_of_isCofibrationSequence (a b : ℤ)
    (S : ShortComplex (AmbientAcyclicWindow F a b))
    (hSeq : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibrationSequence S.f S.g) (p : ℤ) :
    IsAdmissibleExact (termRow F a b S p) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  obtain ⟨hcof, h, q, hPush⟩ := hSeq
  have hAdm : ambientAcyclicWindowCofibrations F a b S.f :=
    (ambientAcyclicWindow_isCofibration_iff F a b S.f).mp hcof
  have hTerm : IsPushout (h.hom.hom.hom.f p) (S.f.hom.hom.hom.f p)
      (q.hom.hom.hom.f p) (S.g.hom.hom.hom.f p) :=
    (ambientAcyclicWindowPushout_term F a b hAdm hPush.flip p).flip
  have hZero : IsZero (((0 : AmbientAcyclicWindow F a b).obj.obj.obj).X p) :=
    (ambientAcyclicWindowRaw F a b ⋙ HomologicalComplex.eval E (.up ℤ) p).map_isZero
      (isZero_zero (AmbientAcyclicWindow F a b))
  let e := hZero.isoZero
  have hTerm' : IsPushout (h.hom.hom.hom.f p ≫ e.hom) (S.f.hom.hom.hom.f p)
      (e.inv ≫ q.hom.hom.hom.f p) (S.g.hom.hom.hom.f p) :=
    hTerm.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  apply ExactCategory.isAdmissibleExact_of_isCofibrationSequence
  exact ⟨((ambientAcyclicWindow_isCofibration_iff F a b S.f).mp hcof) p,
    h.hom.hom.hom.f p ≫ e.hom, e.inv ≫ q.hom.hom.hom.f p, hTerm'⟩

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. Applying
source cycles to a cofibration sequence in the degreewise-admissible and isomorphism-weak window
model gives an admissible exact sequence in E. -/
theorem row_isAdmissibleExact_of_isCofibrationSequence (a b j : ℤ)
    (S : ShortComplex (AmbientAcyclicWindow F a b))
    (hSeq : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibrationSequence S.f S.g) :
    IsAdmissibleExact (row F hKernelClosure a b j S) :=
  row_isAdmissibleExact F hKernelClosure a b j S
    (termRow_isAdmissibleExact_of_isCofibrationSequence F a b S hSeq)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. A
cofibration f in the degreewise-admissible window model induces an admissible mono Zʲ(f) in E. -/
theorem map_isAdmissibleMono (a b j : ℤ) {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L)
    (hf : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration f) : IsAdmissibleMono (map F hKernelClosure a b j f) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  have hAdm : ambientAcyclicWindowCofibrations F a b f :=
    (ambientAcyclicWindow_isCofibration_iff F a b f).mp hf
  obtain ⟨Q, inL, inZero, hQ, _, _, _, _, _⟩ :=
    exists_ambientAcyclicWindowPushout F a b f (0 : K ⟶ (0 : AmbientAcyclicWindow F a b)) hAdm
  have w : f ≫ inL = 0 := by simpa only [zero_comp] using hQ.w
  let S : ShortComplex (AmbientAcyclicWindow F a b) := ShortComplex.mk f inL w
  have hS : IsCofibrationSequence S.f S.g :=
    ⟨hf, 0, inZero, hQ.flip⟩
  exact ExactCategory.isAdmissibleMono_f
    (row_isAdmissibleExact_of_isCofibrationSequence F hKernelClosure a b j S hS)

private theorem compatibleConflations_isPushout {X Y Z P Q : E}
    (t : X ⟶ Y) (l : X ⟶ Z) (r : Y ⟶ P) (b : Z ⟶ P)
    (p : Y ⟶ Q) (q : P ⟶ Q) (wt : t ≫ p = 0) (wb : b ≫ q = 0)
    (h₁ : IsAdmissibleExact (ShortComplex.mk t p wt))
    (h₂ : IsAdmissibleExact (ShortComplex.mk b q wb))
    (hcomm : t ≫ r = l ≫ b) (hquot : r ≫ q = p) : IsPushout t l r b := by
  let S₁ : ShortComplex E := ShortComplex.mk t p wt
  let S₂ : ShortComplex E := ShortComplex.mk b q wb
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk l r (𝟙 Q)
    (by change l ≫ b = t ≫ r; exact hcomm.symm)
    (by change r ≫ q = p ≫ 𝟙 Q; simpa only [Category.comp_id] using hquot)
  let _ : IsIso φ.τ₃ := by
    change IsIso (𝟙 Q)
    infer_instance
  exact isPushout_f_of_isAdmissibleExact_of_isIso_right φ h₁ h₂

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. A given
pushout square in the F-acyclic window along a degreewise-admissible cofibration remains a
pushout square after applying degree-j source cycles. -/
theorem map_isPushout (a b j : ℤ) {K L M P : AmbientAcyclicWindow F a b}
    {i : K ⟶ L} {f : K ⟶ M} {inL : L ⟶ P} {inM : M ⟶ P}
    (hi : letI := ambientAcyclicWindowWaldhausenCategory F a b
      IsCofibration i) (hP : IsPushout i f inL inM) :
    IsPushout (map F hKernelClosure a b j i) (map F hKernelClosure a b j f)
      (map F hKernelClosure a b j inL) (map F hKernelClosure a b j inM) := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  have hAdm : ambientAcyclicWindowCofibrations F a b i :=
    (ambientAcyclicWindow_isCofibration_iff F a b i).mp hi
  obtain ⟨C, q, inZero, hC, _, _, _, _, _⟩ :=
    exists_ambientAcyclicWindowPushout F a b i (0 : K ⟶ (0 : AmbientAcyclicWindow F a b)) hAdm
  have wiq : i ≫ q = 0 := by simpa only [zero_comp] using hC.w
  let S₁ : ShortComplex (AmbientAcyclicWindow F a b) := ShortComplex.mk i q wiq
  have hSeq : IsCofibrationSequence S₁.f S₁.g := ⟨hi, 0, inZero, hC.flip⟩
  have hTerms₁ (p : ℤ) : IsAdmissibleExact (termRow F a b S₁ p) :=
    termRow_isAdmissibleExact_of_isCofibrationSequence F a b S₁ hSeq p
  let g : P ⟶ C := hP.desc q 0 (by simpa only [comp_zero] using wiq)
  have hgL : inL ≫ g = q := hP.inl_desc _ _ _
  have hgM : inM ≫ g = 0 := hP.inr_desc _ _ _
  let S₂ : ShortComplex (AmbientAcyclicWindow F a b) := ShortComplex.mk inM g hgM
  have hTerms₂ (p : ℤ) : IsAdmissibleExact (termRow F a b S₂ p) := by
    change IsAdmissibleExact
      (ShortComplex.mk (inM.hom.hom.hom.f p) (g.hom.hom.hom.f p) _)
    let hTerm := ambientAcyclicWindowPushout_term F a b hAdm hP p
    let w : i.hom.hom.hom.f p ≫ q.hom.hom.hom.f p = 0 := (termRow F a b S₁ p).zero
    let m := pushoutQuotientMap (f.hom.hom.hom.f p) (i.hom.hom.hom.f p)
      (q.hom.hom.hom.f p) (inM.hom.hom.hom.f p) (inL.hom.hom.hom.f p) w hTerm.flip
    have hmL : inL.hom.hom.hom.f p ≫ m = q.hom.hom.hom.f p :=
      pushoutQuotientMap_y _ _ _ _ _ _ _
    have hmM : inM.hom.hom.hom.f p ≫ m = 0 := pushoutQuotientMap_x _ _ _ _ _ _ _
    have hgpL : inL.hom.hom.hom.f p ≫ g.hom.hom.hom.f p = q.hom.hom.hom.f p :=
      congrArg (fun z : L ⟶ C => z.hom.hom.hom.f p) hgL
    have hgpM : inM.hom.hom.hom.f p ≫ g.hom.hom.hom.f p = 0 :=
      congrArg (fun z : M ⟶ C => z.hom.hom.hom.f p) hgM
    have hm : m = g.hom.hom.hom.f p :=
      hTerm.hom_ext (hmL.trans hgpL.symm) (hmM.trans hgpM.symm)
    have hRow : IsAdmissibleExact (ShortComplex.mk (inM.hom.hom.hom.f p) m hmM) :=
      isAdmissibleExact_pushoutQuotientMap (f.hom.hom.hom.f p) (i.hom.hom.hom.f p)
        (q.hom.hom.hom.f p) (inM.hom.hom.hom.f p) (inL.hom.hom.hom.f p) w
        (hTerms₁ p) hTerm.flip
    simpa only [hm] using hRow
  have hCycle₁ : IsAdmissibleExact (row F hKernelClosure a b j S₁) :=
    row_isAdmissibleExact F hKernelClosure a b j S₁ hTerms₁
  have hCycle₂ : IsAdmissibleExact (row F hKernelClosure a b j S₂) :=
    row_isAdmissibleExact F hKernelClosure a b j S₂ hTerms₂
  have hcomm : map F hKernelClosure a b j i ≫ map F hKernelClosure a b j inL =
      map F hKernelClosure a b j f ≫ map F hKernelClosure a b j inM := by
    simpa only [map_comp] using congrArg (map F hKernelClosure a b j) hP.w
  have hquot : map F hKernelClosure a b j inL ≫ map F hKernelClosure a b j g =
      map F hKernelClosure a b j q := by
    simpa only [map_comp] using congrArg (map F hKernelClosure a b j) hgL
  exact compatibleConflations_isPushout
    (map F hKernelClosure a b j i) (map F hKernelClosure a b j f)
    (map F hKernelClosure a b j inL) (map F hKernelClosure a b j inM)
    (map F hKernelClosure a b j q) (map F hKernelClosure a b j g)
    (row F hKernelClosure a b j S₁).zero (row F hKernelClosure a b j S₂).zero
    hCycle₁ hCycle₂ hcomm hquot

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and fully faithful. Assume F reflects admissible exactness, and the kernel of every epi
between objects in its essential image also belongs to that image. Assume F is exact. The source
cycle functor is Waldhausen exact from the window model with degreewise admissible cofibrations
and isomorphism weak maps to the exact-category model on E. -/
theorem functor_isWaldhausenExact (a b j : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := ExactCategory.waldhausenCategory E
    (functor F hKernelClosure a b j).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := ExactCategory.waldhausenCategory E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact map_isZero F hKernelClosure a b j K hK
  · intro K L f hf
    exact map_isAdmissibleMono F hKernelClosure a b j f hf
  · intro K L f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    change IsIso ((functor F hKernelClosure a b j).map f)
    exact Functor.map_isIso (functor F hKernelClosure a b j) f
  · intro K L M P i f inM inL hi hP
    exact (map_isPushout F hKernelClosure a b j hi hP.flip).flip

end CochainComplex.Bounded.AmbientWindowCycles

end
