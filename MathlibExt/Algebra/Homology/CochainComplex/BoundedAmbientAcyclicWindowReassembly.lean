/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicWindowCycleComparison
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowGluing
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowTopIteration
public import MathlibExt.CategoryTheory.Waldhausen.FinCoproductFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequenceComposition
public import Mathlib.CategoryTheory.Whiskering

/-!
# Finite signed-disk reassembly and top-truncation towers

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. The F-acyclic [a,b] window has degreewise admissible cofibrations and
isomorphism weak maps. Put L=(b−a).toNat and dᵢ=b−i for i∈Fin L; these are the degrees a+1
through b. A finite family Xᵢ is reassembled as the selected coproduct R(X)=⊔ᵢD^(dᵢ)(Xᵢ) of
supported identity disks.

Assume additionally that F is fully faithful, reflects admissible exactness, and its essential
image is closed under epi kernels between its objects. The active source-cycle functor
Z(K)=(Z^(dᵢ)(K))ᵢ satisfies R⋙Z≅id on finite E-families. The coordinate maps are the descendants
of matching disk-cycle charts, with zero on every other summand; their inverses use the matching
cycle injections.

Repeated top truncation gives exact stages Tₙ supported in [a,b−n], natural cofiber steps
T̄ₙ₊₁→T̄ₙ→Dₙ in the original window and the zero terminal stage T_L. For n<L, top evaluation
identifies Dₙ with the supported disk on the original cycle Z^(b−n). Suffixes with n+k=L retain
the coordinates n+i, have zero empty value and the binary head-and-tail recurrence.

E and A retain independent object and Hom universes. The definitions include singleton and
reversed windows, where the active coordinate family is empty.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientWindowReassembly

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The active coordinate count is L,
the number of integer degrees a<p≤b. -/
def length (a b : ℤ) : ℕ := (b - a).toNat

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Coordinate i has cycle degree dᵢ, in
descending order from the upper endpoint b. -/
def degree (a b : ℤ) (i : Fin (length a b)) : ℤ := AmbientCycles.degree b i.val

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The recursively defined degree of
coordinate i is exactly b−i. -/
theorem degree_eq (a b : ℤ) (i : Fin (length a b)) : degree a b i = b - (i.val : ℤ) :=
  AmbientCycles.degree_eq b i.val

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Each active disk degree satisfies
a≤dᵢ−1 and dᵢ≤b, so its two terms fit the supplied window. -/
theorem degree_mem (a b : ℤ) (i : Fin (length a b)) :
    a ≤ degree a b i - 1 ∧ degree a b i ≤ b := by
  have hi := i.isLt
  simp only [degree_eq]
  dsimp only [length] at hi
  omega

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Distinct active coordinates have
distinct integer degrees dᵢ. -/
theorem degree_injective (a b : ℤ) : Function.Injective (degree a b) := by
  intro i j h
  apply Fin.ext
  rw [degree_eq, degree_eq] at h
  omega

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For every integer p with a<p≤b,
there is an i∈Fin L with dᵢ=p. -/
theorem exists_degree (a b p : ℤ) (ha : a < p) (hb : p ≤ b) :
    ∃ i : Fin (length a b), degree a b i = p := by
  have hi : (b - p).toNat < length a b := by dsimp only [length]; omega
  refine ⟨⟨(b - p).toNat, hi⟩, ?_⟩
  rw [degree_eq]
  change b - ((b - p).toNat : ℤ) = p
  omega

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The active coordinate set is empty
exactly when b≤a. -/
theorem length_eq_zero_iff (a b : ℤ) : length a b = 0 ↔ b ≤ a := by
  dsimp only [length]
  omega

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.IsExact]

/-- For an exact preadditive category E with zero and binary biproducts, use the Waldhausen model
with admissible monos as cofibrations and isomorphisms as weak equivalences. -/
@[instance_reducible]
local instance exactModel : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. This is the
specified Waldhausen structure on the acyclic support window C(a,b). -/
@[instance_reducible]
local instance windowModel (a b : ℤ) : WaldhausenCategoryWithoutGluing (AmbientAcyclicWindow F a b) :=
  ambientAcyclicWindowWaldhausenCategory F a b

/-- For an exact preadditive category E with zero and binary biproducts and n∈ℕ, the category Fin
n→E has the componentwise Waldhausen model, with admissible-mono cofibrations and isomorphism
weak maps. -/
@[instance_reducible]
local instance piExactModel (n : ℕ) : WaldhausenCategoryWithoutGluing (Fin n → E) :=
  piWaldhausen (fun _ : Fin n => E)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For n∈ℕ, finite
families Fin n→C(a,b) carry the componentwise Waldhausen model. -/
@[instance_reducible]
local instance piWindowModel (a b : ℤ) (n : ℕ) :
    WaldhausenCategoryWithoutGluing (Fin n → AmbientAcyclicWindow F a b) :=
  piWaldhausen (fun _ : Fin n => AmbientAcyclicWindow F a b)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. Weak isomorphisms
satisfy the Waldhausen gluing axiom for admissible pushout squares in C(a,b). -/
theorem gluing (a b : ℤ) : WaldhausenGluingAxiom (C := AmbientAcyclicWindow F a b) := by
  let _ := windowWaldhausenCategory E a b
  let J := ambientAcyclicWindowι F a b
  let hJ := ambientAcyclicWindowι_isWaldhausenExact F a b
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' wi wf wY wZ hx hy hz
  have hp : IsWeakEquivalence (J.map p) := (windowGluing E a b).gluing
    (hJ.map_pushout i f inZ inY hi hP.flip).flip
    (hJ.map_pushout i' f' inZ' inY' hi' hP'.flip).flip
    (J.map x) (J.map y) (J.map z) (J.map p)
    (hJ.map_cofibration i hi) (hJ.map_cofibration i' hi')
    (congrArg (fun t : X ⟶ Y' => t.hom) wi)
    (congrArg (fun t : X ⟶ Z' => t.hom) wf)
    (congrArg (fun t : Y ⟶ P' => t.hom) wY)
    (congrArg (fun t : Z ⟶ P' => t.hom) wZ)
    (hJ.map_weakEquivalence x hx) (hJ.map_weakEquivalence y hy)
    (hJ.map_weakEquivalence z hz)
  exact (ambientAcyclicWindow_isWeakEquivalence_iff F a b p).mpr
    ((ObjectProperty.isIso_hom_iff p).mp ((window_isWeakEquivalence_iff E a b p.hom).mp hp))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Coordinate i assigns X∈E to the supported identity
disk D^(dᵢ)(X), with its positive identity differential under the two term charts. -/
def disk (a b : ℤ) (i : Fin (length a b)) : E ⥤ AmbientAcyclicWindow F a b :=
  SignedDisk.ambient E F a b (degree a b i) (degree_mem a b i).1 (degree_mem a b i).2

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For each i∈Fin L, the supported identity-disk functor
E→C(a,b) in degree dᵢ is Waldhausen exact. -/
theorem disk_isWaldhausenExact (a b : ℤ) (i : Fin (length a b)) :
    (disk F a b i).IsWaldhausenExact :=
  SignedDisk.ambient_isWaldhausenExact E F a b (degree a b i)
    (degree_mem a b i).1 (degree_mem a b i).2

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Send a finite family Xᵢ to the family of supported
identity disks D^(dᵢ)(Xᵢ). -/
def disks (a b : ℤ) : (Fin (length a b) → E) ⥤
    (Fin (length a b) → AmbientAcyclicWindow F a b) :=
  Functor.pi' (fun i => Pi.eval (fun _ : Fin (length a b) => E) i ⋙ disk F a b i)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The finite disk-family functor is Waldhausen exact in
the componentwise product models. -/
theorem disks_isWaldhausenExact (a b : ℤ) : (disks F a b).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.pi' (fun _ : Fin (length a b) => AmbientAcyclicWindow F a b) _
    (fun i => (Pi.eval_isWaldhausenExact (fun _ : Fin (length a b) => E) i).comp
      (disk_isWaldhausenExact F a b i))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Reassemble X∈E^(Fin L) as the selected finite
coproduct R(X)=⊔ᵢD^(dᵢ)(Xᵢ) in C(a,b). -/
def reassembly (a b : ℤ) : (Fin (length a b) → E) ⥤ AmbientAcyclicWindow F a b :=
  disks F a b ⋙ waldhausenFinCoproductFunctor (AmbientAcyclicWindow F a b) (length a b)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The finite disk-reassembly functor R:E^(Fin L)→C(a,b)
is Waldhausen exact. -/
theorem reassembly_isWaldhausenExact (a b : ℤ) : (reassembly F a b).IsWaldhausenExact :=
  (disks_isWaldhausenExact F a b).comp
    (waldhausenFinCoproductFunctor_isWaldhausenExact (AmbientAcyclicWindow F a b)
      (gluing F a b) (length a b))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The selected finite coproduct R(X) has its cofan of
injections ηᵢ:D^(dᵢ)(Xᵢ)→R(X), one for every active coordinate. -/
@[implicit_reducible]
def cofan (a b : ℤ) (X : Fin (length a b) → E) : Cofan ((disks F a b).obj X) :=
  waldhausenFinCoproductCofan (AmbientAcyclicWindow F a b) (length a b) ((disks F a b).obj X)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The cofan of disk injections into R(X) is colimiting,
so any family of maps from these disks has a unique descent from R(X). -/
def cofanIsColimit (a b : ℤ) (X : Fin (length a b) → E) : IsColimit (cofan F a b X) :=
  waldhausenFinCoproductCofanIsColimit (AmbientAcyclicWindow F a b) (length a b)
    ((disks F a b).obj X)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The i-th selected coproduct injection is
ηᵢ:D^(dᵢ)(Xᵢ)→R(X). -/
def injection (a b : ℤ) (X : Fin (length a b) → E) (i : Fin (length a b)) :
    (disk F a b i).obj (X i) ⟶ (reassembly F a b).obj X := (cofan F a b X).inj i

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. Every disk injection ηᵢ:D^(dᵢ)(Xᵢ)→R(X) is a
cofibration in C(a,b). -/
theorem injection_isCofibration (a b : ℤ) (X : Fin (length a b) → E)
    (i : Fin (length a b)) : IsCofibration (injection F a b X i) :=
  waldhausenFinCoproductInjection_isCofibration (AmbientAcyclicWindow F a b) (length a b)
    ((disks F a b).obj X) i

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For integers a,b,
put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For a family map f:X→Y, ηXᵢ≫R(f)=D^(dᵢ)(fᵢ)≫ηYᵢ. -/
theorem injection_naturality (a b : ℤ) {X Y : Fin (length a b) → E} (f : X ⟶ Y)
    (i : Fin (length a b)) :
    injection F a b X i ≫ (reassembly F a b).map f =
      (disk F a b i).map (f i) ≫ injection F a b Y i :=
  waldhausenFinCoproductInjection_naturality (AmbientAcyclicWindow F a b) (length a b)
    ((disks F a b).obj X) ((disks F a b).obj Y) ((disks F a b).map f) i

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L.
The active-cycle functor sends K∈C(a,b) to the family (Z^(dᵢ)(K))ᵢ in E^(Fin L). -/
def cycles (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ (Fin (length a b) → E) :=
  Functor.pi' (fun i => AmbientWindowCycles.functor F hKernelClosure a b (degree a b i))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. The active-cycle family functor is Waldhausen exact for the window model and
the componentwise exact-category model on E^(Fin L). -/
theorem cycles_isWaldhausenExact (a b : ℤ) : (cycles F hKernelClosure a b).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.pi' (fun _ : Fin (length a b) => E) _
    (fun i => AmbientWindowCycles.functor_isWaldhausenExact F hKernelClosure a b (degree a b i))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L.
The i-th supported disk followed by degree-dᵢ source cycles is naturally isomorphic to the
identity of E. -/
@[implicit_reducible]
def selfNatIso (a b : ℤ) (i : Fin (length a b)) :
    disk F a b i ⋙ AmbientWindowCycles.functor F hKernelClosure a b (degree a b i) ≅ 𝟭 E :=
  AmbientWindowCycleComparison.signedDiskNatIso F hKernelClosure a b (degree a b i)
    (degree_mem a b i).1 (degree_mem a b i).2

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L.
The selected cycle Z^(dᵢ)(D^(dᵢ)(X)) is isomorphic to X by the upper-disk term chart. -/
@[implicit_reducible]
def selfIso (a b : ℤ) (i : Fin (length a b)) (X : E) :
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b i)).obj
      ((disk F a b i).obj X) ≅ X := (selfNatIso F hKernelClosure a b i).app X

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L.
If i≠j, the degree-dⱼ source cycle of D^(dᵢ)(Xᵢ) is zero. -/
theorem diskCycle_isZero_off (a b : ℤ) (X : Fin (length a b) → E)
    (i j : Fin (length a b)) (h : i ≠ j) :
    IsZero ((AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).obj
      ((disk F a b i).obj (X i))) :=
  AmbientWindowCycleComparison.signedDisk_isZero_off F hKernelClosure a b (degree a b i)
    (degree_mem a b i).1 (degree_mem a b i).2 (X i) (degree a b j)
    (fun hdeg => h (degree_injective a b hdeg).symm)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. Apply the degree-p cycle functor to the selected reassembly cofan. Its apex
is Zᵖ(R(X)) and its legs are the cycle maps of the disk injections. -/
@[implicit_reducible]
def cycleCofan (a b : ℤ) (X : Fin (length a b) → E) (p : ℤ) :
    Cofan (fun i => (AmbientWindowCycles.functor F hKernelClosure a b p).obj
      ((disk F a b i).obj (X i))) :=
  Cofan.mk ((AmbientWindowCycles.functor F hKernelClosure a b p).obj ((reassembly F a b).obj X))
    (fun i => (AmbientWindowCycles.functor F hKernelClosure a b p).map (injection F a b X i))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The i-th leg of the mapped degree-p cycle cofan is Zᵖ(ηᵢ). -/
theorem cycleCofan_inj (a b : ℤ) (X : Fin (length a b) → E) (p : ℤ)
    (i : Fin (length a b)) :
    (cycleCofan F hKernelClosure a b X p).inj i =
      (AmbientWindowCycles.functor F hKernelClosure a b p).map (injection F a b X i) := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. Exactness of the source-cycle functor makes the mapped finite degree-p cycle
cofan colimiting. -/
def cycleCofanIsColimit (a b : ℤ) (X : Fin (length a b) → E) (p : ℤ) :
    IsColimit (cycleCofan F hKernelClosure a b X p) :=
  (AmbientWindowCycles.functor_isWaldhausenExact F hKernelClosure a b p).mapFinCofanIsColimit
    (cofan F a b X) (cofanIsColimit F a b X)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. For coordinate j, use the chart Z^(dⱼ)(Dᵈʲ(Xⱼ))→Xⱼ on the matching summand
and zero on each nonmatching summand. -/
def descentLegs (a b : ℤ) (X : Fin (length a b) → E) (j : Fin (length a b)) :
    ∀ i : Fin (length a b),
      (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).obj
        ((disk F a b i).obj (X i)) ⟶ X j := by
  classical
  intro i
  by_cases h : i = j
  · subst i
    exact (selfIso F hKernelClosure a b j (X j)).hom
  · exact 0

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The matching descent leg in coordinate j is exactly the signed-disk
source-cycle chart to Xⱼ. -/
theorem descentLegs_self (a b : ℤ) (X : Fin (length a b) → E) (j : Fin (length a b)) :
    descentLegs F hKernelClosure a b X j j = (selfIso F hKernelClosure a b j (X j)).hom := by
  classical
  simp [descentLegs]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. Descend the matching/zero cycle-cofan legs to obtain πⱼ:Z^(dⱼ)(R(X))→Xⱼ. -/
def projection (a b : ℤ) (X : Fin (length a b) → E) (j : Fin (length a b)) :
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).obj
      ((reassembly F a b).obj X) ⟶ X j :=
  Cofan.IsColimit.desc (cycleCofanIsColimit F hKernelClosure a b X (degree a b j))
    (descentLegs F hKernelClosure a b X j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The inverse coordinate map Xⱼ→Z^(dⱼ)(R(X)) is the inverse disk-cycle chart
followed by the cycle map of ηⱼ. -/
@[implicit_reducible]
def sectionMap (a b : ℤ) (X : Fin (length a b) → E) (j : Fin (length a b)) :
    X j ⟶ (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).obj
      ((reassembly F a b).obj X) :=
  (selfIso F hKernelClosure a b j (X j)).inv ≫
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).map
      (injection F a b X j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. For all i,j, Z^(dⱼ)(ηᵢ)≫πⱼ equals the matching disk-cycle chart when i=j, and
the zero descent leg otherwise. -/
theorem projection_fac (a b : ℤ) (X : Fin (length a b) → E) (i j : Fin (length a b)) :
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).map
        (injection F a b X i) ≫ projection F hKernelClosure a b X j =
      descentLegs F hKernelClosure a b X j i :=
  Cofan.IsColimit.fac (cycleCofanIsColimit F hKernelClosure a b X (degree a b j))
    (descentLegs F hKernelClosure a b X j) i

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The cofan projection πⱼ and matching inverse cycle injection give
Z^(dⱼ)(R(X))≅Xⱼ. -/
def returnIso (a b : ℤ) (X : Fin (length a b) → E) (j : Fin (length a b)) :
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).obj
      ((reassembly F a b).obj X) ≅ X j where
  hom := projection F hKernelClosure a b X j
  inv := sectionMap F hKernelClosure a b X j
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext
      (cycleCofanIsColimit F hKernelClosure a b X (degree a b j))
    intro i
    rw [cycleCofan_inj, ← Category.assoc, projection_fac]
    by_cases h : i = j
    · subst i
      rw [descentLegs_self]
      change _ ≫ (_ ≫ _) = _ ≫ 𝟙 _
      simp only [Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (diskCycle_isZero_off F hKernelClosure a b X i j h).eq_of_src _ _
  inv_hom_id := by
    change (_ ≫ _) ≫ _ = 𝟙 _
    rw [Category.assoc, projection_fac, descentLegs_self, Iso.inv_hom_id]

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. For f:X→Y, the cycle image of ηXᵢ followed by Zᵖ(R(f)) equals Zᵖ(D^(dᵢ)(fᵢ))
followed by the cycle image of ηYᵢ. -/
theorem cycleInjection_naturality (a b : ℤ) {X Y : Fin (length a b) → E} (f : X ⟶ Y)
    (p : ℤ) (i : Fin (length a b)) :
    (AmbientWindowCycles.functor F hKernelClosure a b p).map (injection F a b X i) ≫
        (AmbientWindowCycles.functor F hKernelClosure a b p).map ((reassembly F a b).map f) =
      (AmbientWindowCycles.functor F hKernelClosure a b p).map ((disk F a b i).map (f i)) ≫
        (AmbientWindowCycles.functor F hKernelClosure a b p).map (injection F a b Y i) := by
  simpa only [AmbientWindowCycles.map_comp] using
    congrArg (AmbientWindowCycles.map F hKernelClosure a b p) (injection_naturality F a b f i)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. For f:X→Y, Z^(dⱼ)(R(f))≫πYⱼ=πXⱼ≫fⱼ. -/
theorem projection_naturality (a b : ℤ) {X Y : Fin (length a b) → E} (f : X ⟶ Y)
    (j : Fin (length a b)) :
    (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).map
        ((reassembly F a b).map f) ≫ projection F hKernelClosure a b Y j =
      projection F hKernelClosure a b X j ≫ f j := by
  apply Cofan.IsColimit.hom_ext
    (cycleCofanIsColimit F hKernelClosure a b X (degree a b j))
  intro i
  rw [cycleCofan_inj, ← Category.assoc, cycleInjection_naturality, Category.assoc,
    projection_fac, ← Category.assoc, projection_fac]
  by_cases h : i = j
  · subst i
    rw [descentLegs_self, descentLegs_self]
    exact (selfNatIso F hKernelClosure a b j).hom.naturality (f j)
  · exact (diskCycle_isZero_off F hKernelClosure a b X i j h).eq_of_src _ _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. Reassembly followed by active cycles and evaluation at j is naturally
isomorphic to evaluation at j in E^(Fin L). -/
def coordinateNatIso (a b : ℤ) (j : Fin (length a b)) :
    reassembly F a b ⋙ cycles F hKernelClosure a b ⋙
      Pi.eval (fun _ : Fin (length a b) => E) j ≅
        Pi.eval (fun _ : Fin (length a b) => E) j :=
  NatIso.ofComponents (fun X => returnIso F hKernelClosure a b X j)
    (fun f => projection_naturality F hKernelClosure a b f j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The coordinate charts assemble into the natural isomorphism R⋙Z≅id on E^(Fin
L). -/
def reassemblyCyclesNatIso (a b : ℤ) :
    reassembly F a b ⋙ cycles F hKernelClosure a b ≅ 𝟭 (Fin (length a b) → E) :=
  NatIso.pi' (fun j => coordinateNatIso F hKernelClosure a b j)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The forward component of R⋙Z≅id at family X and coordinate j is the cofan
projection πⱼ. -/
theorem reassemblyCyclesNatIso_hom_app (a b : ℤ) (X : Fin (length a b) → E)
    (j : Fin (length a b)) :
    (reassemblyCyclesNatIso F hKernelClosure a b).hom.app X j =
      projection F hKernelClosure a b X j := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. Write R(X)=⊔ᵢD^(dᵢ)(Xᵢ) for the selected finite disk reassembly and
Z(K)=(Z^(dᵢ)(K))ᵢ. The inverse component of R⋙Z≅id at X,j is the inverse matching disk-cycle
chart followed by Z^(dⱼ)(ηⱼ). -/
theorem reassemblyCyclesNatIso_inv_app (a b : ℤ) (X : Fin (length a b) → E)
    (j : Fin (length a b)) :
    (reassemblyCyclesNatIso F hKernelClosure a b).inv.app X j =
      (selfIso F hKernelClosure a b j (X j)).inv ≫
        (AmbientWindowCycles.functor F hKernelClosure a b (degree a b j)).map
          (injection F a b X j) := rfl

omit [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be preadditive, A abelian and F:E→A additive. For c≤b, an F-acyclic complex supported in
[a,c] is also supported in [a,b], giving the inclusion C(a,c)→C(a,b). -/
def includeWindow (a c b : ℤ) (hc : c ≤ b) :
    AmbientAcyclicWindow F a c ⥤ AmbientAcyclicWindow F a b :=
  ObjectProperty.lift (ambientAcyclicWindowObjects F a b)
    (ambientAcyclicWindowι F a c ⋙ windowInclude E a c a b le_rfl hc)
    (fun K => K.property)

omit [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For c≤b, the
support-only inclusion C(a,c)→C(a,b) is Waldhausen exact in the isomorphism-weak window models. -/
theorem includeWindow_isWaldhausenExact (a c b : ℤ) (hc : c ≤ b) :
    (includeWindow F a c b hc).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a c
  let _ := windowWaldhausenCategory E a b
  let h := (ambientAcyclicWindowι_isWaldhausenExact F a c).comp
    (windowInclude_isWaldhausenExact E a c a b le_rfl hc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowι F a b) _
      (h.map_isZero hK)
  · intro K L f hf
    apply (ambientAcyclicWindow_isCofibration_iff F a b _).mpr
    exact (window_isCofibration_iff E a b _).mp (h.map_cofibration f hf)
  · intro K L f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a c f).mp hf
    exact (ambientAcyclicWindow_isWeakEquivalence_iff F a b _).mpr inferInstance
  · intro K L M P i f inM inL hi hP
    exact IsPushout.of_map_of_faithful (ambientAcyclicWindowι F a b)
      (h.map_pushout i f inM inL hi hP)

/-- For an integer b and n∈ℕ, the decreasing endpoint b−n is at most b. -/
theorem endpoint_le (b : ℤ) (n : ℕ) : AmbientCycles.degree b n ≤ b := by
  rw [AmbientCycles.degree_eq]
  omega

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). Define T₀ as identity and
Tₙ₊₁ by applying shorter-window top truncation to Tₙ at its endpoint b−n. -/
def tower (a b : ℤ) : (n : ℕ) →
    AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a (AmbientCycles.degree b n) :=
  Nat.rec (𝟭 (AmbientAcyclicWindow F a b))
    (fun n T => T ⋙ AmbientWindowTruncation.shorterFunctor F hKernelClosure a
      (AmbientCycles.degree b n))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The zero stage T₀ is the
identity functor of C(a,b). -/
theorem tower_zero (a b : ℤ) : tower F hKernelClosure a b 0 = 𝟭 (AmbientAcyclicWindow F a b) :=
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The successor is Tₙ
followed by shorter-window top truncation at b−n. -/
theorem tower_succ (a b : ℤ) (n : ℕ) :
    tower F hKernelClosure a b (n + 1) = tower F hKernelClosure a b n ⋙
      AmbientWindowTruncation.shorterFunctor F hKernelClosure a (AmbientCycles.degree b n) :=
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). Every stage
Tₙ:C(a,b)→C(a,b−n) is Waldhausen exact. -/
theorem tower_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    (tower F hKernelClosure a b n).IsWaldhausenExact := by
  induction n with
  | zero => exact Functor.IsWaldhausenExact.id
  | succ n ih =>
    exact ih.comp (AmbientWindowTruncation.shorterFunctor_isWaldhausenExact
      F hKernelClosure a (AmbientCycles.degree b n))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). Each term of Tₙ(K) is zero
outside [a,b−n], for all n∈ℕ and K∈C(a,b). -/
theorem tower_support (a b : ℤ) (n : ℕ) (K : AmbientAcyclicWindow F a b) :
    ∀ p : ℤ, p < a ∨ AmbientCycles.degree b n < p →
      IsZero (((tower F hKernelClosure a b n).obj K).obj.obj.obj.X p) :=
  ((tower F hKernelClosure a b n).obj K).obj.property

/-- Let E be preadditive, A abelian and F:E→A additive. For n∈ℕ, the support inclusion
C(a,b−n)→C(a,b) places the same complex in its original window. -/
def includeOriginal (a b : ℤ) (n : ℕ) :
    AmbientAcyclicWindow F a (AmbientCycles.degree b n) ⥤ AmbientAcyclicWindow F a b :=
  includeWindow F a (AmbientCycles.degree b n) b (endpoint_le b n)

omit [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and exact. Let C(a,b) be the full category of F-acyclic cochains supported in [a,b],
with degreewise admissible-mono cofibrations and isomorphisms as weak maps. For every n∈ℕ, the
inclusion C(a,b−n)→C(a,b) is Waldhausen exact. -/
theorem includeOriginal_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    (includeOriginal F a b n).IsWaldhausenExact :=
  includeWindow_isWaldhausenExact F a (AmbientCycles.degree b n) b (endpoint_le b n)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The included stage T̄ₙ is
Tₙ followed by the support inclusion C(a,b−n)→C(a,b). -/
def originalFunctor (a b : ℤ) (n : ℕ) : AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  tower F hKernelClosure a b n ⋙ includeOriginal F a b n

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The included zero stage T̄₀
is the identity of C(a,b). -/
theorem originalFunctor_zero (a b : ℤ) :
    originalFunctor F hKernelClosure a b 0 = 𝟭 (AmbientAcyclicWindow F a b) := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). Every included stage
T̄ₙ:C(a,b)→C(a,b) is Waldhausen exact. -/
theorem originalFunctor_isWaldhausenExact (a b : ℤ) (n : ℕ) :
    (originalFunctor F hKernelClosure a b n).IsWaldhausenExact :=
  (tower_isWaldhausenExact F hKernelClosure a b n).comp
    (includeOriginal_isWaldhausenExact F a b n)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The included successor
T̄ₙ₊₁ is Tₙ followed by same-window top truncation at b−n and then inclusion into the original
window. -/
theorem originalFunctor_succ (a b : ℤ) (n : ℕ) :
    originalFunctor F hKernelClosure a b (n + 1) = tower F hKernelClosure a b n ⋙
      AmbientWindowTruncation.fullTruncationFunctor F hKernelClosure a (AmbientCycles.degree b n) ⋙
        includeOriginal F a b n := rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The n-th disk stage is the
top identity disk on Tₙ(K)^(b−n), included from its stage window into C(a,b). -/
def diskStage (a b : ℤ) (n : ℕ) : AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  tower F hKernelClosure a b n ⋙ AmbientWindowTruncation.diskFunctor F a
    (AmbientCycles.degree b n) ⋙ includeOriginal F a b n

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The kernel inclusion at
endpoint b−n gives a natural map T̄ₙ₊₁→T̄ₙ in the original window. -/
def inclusionStep (a b : ℤ) (n : ℕ) :
    originalFunctor F hKernelClosure a b (n + 1) ⟶ originalFunctor F hKernelClosure a b n :=
  Functor.whiskerRight (Functor.whiskerLeft (tower F hKernelClosure a b n)
    (AmbientWindowTruncation.kernelInclusion F hKernelClosure a (AmbientCycles.degree b n)))
    (includeOriginal F a b n)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The top-disk projection at
endpoint b−n gives a natural map T̄ₙ→Dₙ to the included n-th disk stage. -/
def projectionStep (a b : ℤ) (n : ℕ) :
    originalFunctor F hKernelClosure a b n ⟶ diskStage F hKernelClosure a b n :=
  Functor.whiskerRight (Functor.whiskerLeft (tower F hKernelClosure a b n)
    (AmbientWindowTruncation.diskProjection F a (AmbientCycles.degree b n)))
    (includeOriginal F a b n)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The natural kernel step and
disk projection give the Waldhausen cofiber sequence of exact endofunctors T̄ₙ₊₁→T̄ₙ→Dₙ. -/
theorem originalCofiberFunctorSequence (a b : ℤ) (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence (originalFunctor F hKernelClosure a b (n + 1))
      (originalFunctor F hKernelClosure a b n) (diskStage F hKernelClosure a b n)
      (inclusionStep F hKernelClosure a b n) (projectionStep F hKernelClosure a b n) :=
  ((AmbientWindowTruncation.cofiberFunctorSequence F hKernelClosure a
    (AmbientCycles.degree b n)).precomp
    (tower F hKernelClosure a b n) (tower_isWaldhausenExact F hKernelClosure a b n)).postcomp
      (includeOriginal_isWaldhausenExact F a b n)

omit [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] [F.IsExact]
  [F.Full] [F.ReflectsAdmissibleExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. If b≤a, every object in the F-acyclic [a,b] window is zero:
the singleton case uses F-acyclicity and the source-cycle charts, and a reversed window has no
supported terms. -/
theorem isZero_of_width_le (a b : ℤ) (hba : b ≤ a) (K : AmbientAcyclicWindow F a b) :
    IsZero K := by
  have hRaw : IsZero K.obj.obj.obj := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.hom_ext
    intro p
    have hTerm : IsZero (K.obj.obj.obj.X p) := by
      by_cases hp : p = b
      · subst p
        exact AmbientWindowTruncation.topTerm_isZero_of_prev F a b K
          (K.obj.property (b - 1) (Or.inl (by omega)))
      · exact K.obj.property p (by omega)
    exact hTerm.eq_of_src _ _
  exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowRaw F a b) K hRaw

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The terminal endpoint b−L is at most
a. -/
theorem terminal_endpoint_le (a b : ℤ) : AmbientCycles.degree b (length a b) ≤ a := by
  rw [AmbientCycles.degree_eq]
  dsimp only [length]
  omega

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The terminal object T_L(K) is zero for every K, because
its endpoint is at most a. -/
theorem terminal_isZero (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsZero ((tower F hKernelClosure a b (length a b)).obj K) :=
  isZero_of_width_le F a (AmbientCycles.degree b (length a b)) (terminal_endpoint_le a b) _

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The included terminal stage T̄_L sends every source object
to zero in C(a,b). -/
theorem original_terminal_isZero (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    IsZero ((originalFunctor F hKernelClosure a b (length a b)).obj K) :=
  (includeOriginal_isWaldhausenExact F a b (length a b)).map_isZero
    (terminal_isZero F hKernelClosure a b K)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For p≤b−n, degree-p cycles
after Tₙ are naturally isomorphic to the original degree-p source cycles of K. -/
def towerCycleNatIso (a b : ℤ) : (n : ℕ) → (p : ℤ) → (hp : p ≤ AmbientCycles.degree b n) →
    tower F hKernelClosure a b n ⋙
      AmbientWindowCycles.functor F hKernelClosure a (AmbientCycles.degree b n) p ≅
        AmbientWindowCycles.functor F hKernelClosure a b p
  | 0, p, _hp => eqToIso (by rfl)
  | n + 1, p, hp =>
    Functor.isoWhiskerLeft (tower F hKernelClosure a b n)
      (AmbientWindowCycleComparison.shorterCycleNatIso F hKernelClosure a (AmbientCycles.degree b n)
        p (by change p ≤ AmbientCycles.degree b n - 1 at hp; omega)) ≪≫
      towerCycleNatIso a b n p
        (by change p ≤ AmbientCycles.degree b n - 1 at hp; omega)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). The top term Tₙ(K)^(b−n) is
naturally isomorphic to the original source cycle Z^(b−n)(K). -/
def topEvaluationNatIso (a b : ℤ) (n : ℕ) :
    tower F hKernelClosure a b n ⋙ ambientAcyclicWindowRaw F a (AmbientCycles.degree b n) ⋙
      HomologicalComplex.eval E (.up ℤ) (AmbientCycles.degree b n) ≅
        AmbientWindowCycles.functor F hKernelClosure a b (AmbientCycles.degree b n) :=
  Functor.isoWhiskerLeft (tower F hKernelClosure a b n)
    (AmbientWindowCycleComparison.topNatIso F hKernelClosure a (AmbientCycles.degree b n)).symm ≪≫
      towerCycleNatIso F hKernelClosure a b n (AmbientCycles.degree b n) le_rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For n<L, the head functor sends K to the supported disk
D^(b−n)(Z^(b−n)(K)) in the original window. -/
def head (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  AmbientWindowCycles.functor F hKernelClosure a b (degree a b ⟨n, hn⟩) ⋙ disk F a b ⟨n, hn⟩

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For n<L, the original-cycle signed-disk head functor is
Waldhausen exact. -/
theorem head_isWaldhausenExact (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    (head F hKernelClosure a b n hn).IsWaldhausenExact :=
  (AmbientWindowCycles.functor_isWaldhausenExact F hKernelClosure a b (degree a b ⟨n, hn⟩)).comp
    (disk_isWaldhausenExact F a b ⟨n, hn⟩)

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For n<L, the included disk stage is top-term evaluation of
Tₙ followed by the supported disk in degree b−n. -/
theorem diskStage_eq (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    diskStage F hKernelClosure a b n =
      (tower F hKernelClosure a b n ⋙ ambientAcyclicWindowRaw F a (AmbientCycles.degree b n) ⋙
        HomologicalComplex.eval E (.up ℤ) (AmbientCycles.degree b n)) ⋙ disk F a b ⟨n, hn⟩ :=
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. Let Tₙ(K) be the iterated top truncation
of K, supported in [a,b−n], and let T̄ₙ include it back into C(a,b). For integers a,b, put
L=(b−a).toNat and dᵢ=b−i for i∈Fin L. For n<L, the top-evaluation cycle chart gives a natural
isomorphism from the disk stage Dₙ to the head disk on Z^(b−n)(K). -/
def diskStageHeadNatIso (a b : ℤ) (n : ℕ) (hn : n < length a b) :
    diskStage F hKernelClosure a b n ≅ head F hKernelClosure a b n hn :=
  eqToIso (diskStage_eq F hKernelClosure a b n hn) ≪≫
    Functor.isoWhiskerRight (topEvaluationNatIso F hKernelClosure a b n) (disk F a b ⟨n, hn⟩)

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. If n+k=L and i∈Fin k, the suffix
coordinate is n+i∈Fin L. -/
def suffixCoordinate (a b : ℤ) (n k : ℕ) (h : n + k = length a b) (i : Fin k) :
    Fin (length a b) := ⟨n + i.val, by have hi := i.isLt; omega⟩

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. The full suffix starting at n=0
sends each coordinate i∈Fin L to i. -/
theorem suffixCoordinate_zero (a b : ℤ) (i : Fin (length a b)) :
    suffixCoordinate a b 0 (length a b) (Nat.zero_add _) i = i := by
  apply Fin.ext
  exact Nat.zero_add _

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. If n+k+1=L, the first coordinate of
the nonempty suffix is n. -/
theorem suffixCoordinate_head (a b : ℤ) (n k : ℕ) (h : n + (k + 1) = length a b) :
    suffixCoordinate a b n (k + 1) h 0 = ⟨n, by omega⟩ := by
  apply Fin.ext
  exact Nat.add_zero _

/-- For integers a,b, put L=(b−a).toNat and dᵢ=b−i for i∈Fin L. If n+k+1=L, suffix coordinate i+1
equals coordinate i of the next suffix starting at n+1. -/
theorem suffixCoordinate_tail (a b : ℤ) (n k : ℕ) (h : n + (k + 1) = length a b) (i : Fin k) :
    suffixCoordinate a b n (k + 1) h i.succ = suffixCoordinate a b (n + 1) k (by omega) i := by
  apply Fin.ext
  dsimp only [suffixCoordinate, Fin.val_succ]
  omega

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. These cycle-evaluated supported disks form a functor C(a,b)→C(a,b)^(Fin k). -/
def suffixFamily (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    AmbientAcyclicWindow F a b ⥤ (Fin k → AmbientAcyclicWindow F a b) :=
  Functor.pi' (fun i =>
    AmbientWindowCycles.functor F hKernelClosure a b (degree a b (suffixCoordinate a b n k h i)) ⋙
      disk F a b (suffixCoordinate a b n k h i))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. The suffix functor takes the selected finite coproduct of this k-coordinate disk family in
C(a,b). -/
def suffix (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    AmbientAcyclicWindow F a b ⥤ AmbientAcyclicWindow F a b :=
  suffixFamily F hKernelClosure a b n k h ⋙
    waldhausenFinCoproductFunctor (AmbientAcyclicWindow F a b) k

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. For n=0,k=L, the full suffix family is active cycles followed by the corresponding supported
disk family. -/
theorem suffixFamily_zero (a b : ℤ) :
    suffixFamily F hKernelClosure a b 0 (length a b) (Nat.zero_add _) =
      cycles F hKernelClosure a b ⋙ disks F a b := by
  apply Functor.pi_ext
  intro i
  change (AmbientWindowCycles.functor F hKernelClosure a b
    (degree a b (suffixCoordinate a b 0 (length a b) (Nat.zero_add _) i)) ⋙
    disk F a b (suffixCoordinate a b 0 (length a b) (Nat.zero_add _) i)) = _
  rw [suffixCoordinate_zero]
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. For n=0,k=L, the full suffix functor is Z followed by reassembly R, namely Z⋙R on C(a,b). -/
theorem suffix_zero_eq (a b : ℤ) :
    suffix F hKernelClosure a b 0 (length a b) (Nat.zero_add _) =
      cycles F hKernelClosure a b ⋙ reassembly F a b := by
  rw [suffix, suffixFamily_zero]
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. When k=0 and n=L, the empty suffix is the constant functor at the selected zero of C(a,b). -/
theorem suffix_terminal (a b : ℤ) (n : ℕ) (h : n + 0 = length a b) :
    suffix F hKernelClosure a b n 0 h =
      (Functor.const (AmbientAcyclicWindow F a b)).obj (0 : AmbientAcyclicWindow F a b) := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Assume F is exact, and put
L=(b−a).toNat. If n+k+1=L, the suffix family with k+1 coordinates starting at n has first
component D^(b−n)(Z^(b−n)(K)). -/
theorem suffixFamily_head (a b : ℤ) (n k : ℕ) (h : n + (k + 1) = length a b) :
    suffixFamily F hKernelClosure a b n (k + 1) h ⋙
      Pi.eval (fun _ : Fin (k + 1) => AmbientAcyclicWindow F a b) 0 =
        head F hKernelClosure a b n (by omega) := by
  change (AmbientWindowCycles.functor F hKernelClosure a b
    (degree a b (suffixCoordinate a b n (k + 1) h 0)) ⋙
      disk F a b (suffixCoordinate a b n (k + 1) h 0)) = _
  rw [suffixCoordinate_head]
  rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Assume F is exact, and put
L=(b−a).toNat. If n+k+1=L, removing the first component of the (k+1)-coordinate suffix starting
at n gives the k-coordinate suffix family starting at n+1. -/
theorem suffixFamily_tail (a b : ℤ) (n k : ℕ) (h : n + (k + 1) = length a b) :
    suffixFamily F hKernelClosure a b n (k + 1) h ⋙ finTail (AmbientAcyclicWindow F a b) k =
      suffixFamily F hKernelClosure a b (n + 1) k (by omega) := by
  apply Functor.pi_ext
  intro i
  change (AmbientWindowCycles.functor F hKernelClosure a b
    (degree a b (suffixCoordinate a b n (k + 1) h i.succ)) ⋙
      disk F a b (suffixCoordinate a b n (k + 1) h i.succ)) = _
  rw [suffixCoordinate_tail]
  rfl

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Assume F is exact, and put
L=(b−a).toNat. If n+k+1=L, the selected (k+1)-coordinate suffix coproduct is the binary
coproduct of its disk head at n and the k-coordinate suffix starting at n+1. -/
theorem suffix_succ (a b : ℤ) (n k : ℕ) (h : n + (k + 1) = length a b) :
    suffix F hKernelClosure a b n (k + 1) h =
      ((head F hKernelClosure a b n (by omega)).prod'
        (suffix F hKernelClosure a b (n + 1) k (by omega))) ⋙
          waldhausenCoproductFunctor (AmbientAcyclicWindow F a b) := by
  unfold suffix
  rw [waldhausenFinCoproductFunctor_succ]
  have hPair : suffixFamily F hKernelClosure a b n (k + 1) h ⋙
      (Pi.eval (fun _ : Fin (k + 1) => AmbientAcyclicWindow F a b) 0).prod'
        (finTail (AmbientAcyclicWindow F a b) k ⋙
          waldhausenFinCoproductFunctor (AmbientAcyclicWindow F a b) k) =
      (head F hKernelClosure a b n (by omega)).prod'
        (suffixFamily F hKernelClosure a b (n + 1) k (by omega) ⋙
          waldhausenFinCoproductFunctor (AmbientAcyclicWindow F a b) k) := by
    change ((suffixFamily F hKernelClosure a b n (k + 1) h ⋙
      Pi.eval (fun _ : Fin (k + 1) => AmbientAcyclicWindow F a b) 0).prod'
      ((suffixFamily F hKernelClosure a b n (k + 1) h ⋙ finTail (AmbientAcyclicWindow F a b) k) ⋙
        waldhausenFinCoproductFunctor (AmbientAcyclicWindow F a b) k)) = _
    rw [suffixFamily_head, suffixFamily_tail]
  exact congrArg (fun T => T ⋙ waldhausenCoproductFunctor (AmbientAcyclicWindow F a b)) hPair

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. The k-coordinate cycle-disk family is Waldhausen exact in the componentwise product model. -/
theorem suffixFamily_isWaldhausenExact (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    (suffixFamily F hKernelClosure a b n k h).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.pi' (fun _ : Fin k => AmbientAcyclicWindow F a b) _
    (fun i =>
      (AmbientWindowCycles.functor_isWaldhausenExact F hKernelClosure a b
        (degree a b (suffixCoordinate a b n k h i))).comp
        (disk_isWaldhausenExact F a b (suffixCoordinate a b n k h i)))

/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian and F:E→A
additive and fully faithful. Assume F reflects admissible exactness and its essential image is
closed under kernels of epimorphisms between its objects. Write Zᵖ(K) for the selected E-cycles
of an F-acyclic supported complex. Assume F is exact. For integers a,b, put L=(b−a).toNat and
dᵢ=b−i for i∈Fin L. For n+k=L, form the suffix family of disks D^(b−n−i)(Z^(b−n−i)(K)) for i∈Fin
k. The selected finite coproduct of the suffix family is a Waldhausen exact endofunctor of
C(a,b). -/
theorem suffix_isWaldhausenExact (a b : ℤ) (n k : ℕ) (h : n + k = length a b) :
    (suffix F hKernelClosure a b n k h).IsWaldhausenExact :=
  (suffixFamily_isWaldhausenExact F hKernelClosure a b n k h).comp
    (waldhausenFinCoproductFunctor_isWaldhausenExact (AmbientAcyclicWindow F a b) (gluing F a b) k)

end CochainComplex.Bounded.AmbientWindowReassembly

end
