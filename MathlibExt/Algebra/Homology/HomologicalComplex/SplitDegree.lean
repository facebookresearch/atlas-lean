/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitHomology
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Degree decompositions of split complexes

Let K be a complex of shape c in a preadditive category and s a splitting.
At a degree i with homology, write Z_i for cycles and π_i : Z_i → H_i for
the homology quotient. The normalized splitting supplies a cycles
retraction and a section of π_i.

If π_i has a kernel B_i, cycles decompose as B_i ⊞ H_i. If the cycles
inclusion j_i : Z_i → K_i has a cokernel Q_i, the term decomposes as
Z_i ⊞ Q_i. If both objects exist, K_i ≅ (B_i ⊞ H_i) ⊞ Q_i, with the
kernel, cycle and quotient maps as its inclusions and projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let rᵢ : Kᵢ → Zᵢ be the
cycles retraction supplied by the normalized splitting. The homology inclusion ℓᵢ : Hᵢ → Kᵢ
supplied by s.normalize, followed by rᵢ, defines the canonical map tᵢ = ℓᵢ ≫ rᵢ : Hᵢ → Zᵢ.
-/
def Splitting.homologyCycleSection (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homology i ⟶ K.cycles i :=
  s.homologyInclusionComponent i ≫ s.cyclesRetraction i

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let rᵢ : Kᵢ → Zᵢ be the
cycles retraction supplied by the normalized splitting. Let tᵢ : Hᵢ → Zᵢ be its
homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. The constructed section is
a right inverse to the quotient: tᵢ ≫ πᵢ = 1_{Hᵢ}.
-/
@[reassoc]
theorem Splitting.homologyCycleSection_homologyπ (s : Splitting K) (i : ι)
    [K.HasHomology i] : s.homologyCycleSection i ≫ K.homologyπ i = 𝟙 (K.homology i) := by
  have hd : K.d (c.prev i) i ≫ s.cyclesRetraction i ≫ K.homologyπ i = 0 := by
    calc
      _ = (K.toCycles (c.prev i) i ≫ K.iCycles i) ≫ s.cyclesRetraction i ≫ K.homologyπ i := by
        exact congrArg (fun f : K.X (c.prev i) ⟶ K.X i =>
          f ≫ s.cyclesRetraction i ≫ K.homologyπ i) (K.toCycles_i (c.prev i) i).symm
      _ = K.toCycles (c.prev i) i ≫ (K.iCycles i ≫ s.cyclesRetraction i) ≫ K.homologyπ i := by
        simp only [Category.assoc]
      _ = K.toCycles (c.prev i) i ≫ K.homologyπ i := by
        rw [s.iCycles_cyclesRetraction i, Category.id_comp]
      _ = 0 := K.toCycles_comp_homologyπ (c.prev i) i
  have hb : prevD i s.normalize.hom ≫ s.cyclesRetraction i ≫ K.homologyπ i = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
      s.cyclesRetraction i ≫ K.homologyπ i = 0
    simp only [Category.assoc, hd, comp_zero]
  apply (cancel_epi (K.homologyπ i)).1
  calc
    K.homologyπ i ≫ (s.homologyCycleSection i ≫ K.homologyπ i) =
        (K.homologyπ i ≫ s.homologyInclusionComponent i) ≫
          s.cyclesRetraction i ≫ K.homologyπ i := by
      simp only [homologyCycleSection, Category.assoc]
    _ = (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) ≫
          s.cyclesRetraction i ≫ K.homologyπ i := by
      rw [s.homologyπ_homologyInclusionComponent i]
    _ = K.iCycles i ≫ s.cyclesRetraction i ≫ K.homologyπ i -
          K.iCycles i ≫ (prevD i s.normalize.hom ≫ s.cyclesRetraction i ≫ K.homologyπ i) := by
      simp only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
        Category.id_comp]
    _ = K.homologyπ i := by
      rw [hb, comp_zero, sub_zero, ← Category.assoc,
        s.iCycles_cyclesRetraction i, Category.id_comp]
    _ = K.homologyπ i ≫ 𝟙 (K.homology i) := (Category.comp_id _).symm

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let rᵢ : Kᵢ → Zᵢ be the
cycles retraction supplied by the normalized splitting. Let tᵢ : Hᵢ → Zᵢ be its
homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. Embedding the homology
section into the term recovers its homology inclusion: tᵢ ≫ jᵢ = ℓᵢ.
-/
@[reassoc]
theorem Splitting.homologyCycleSection_iCycles (s : Splitting K) (i : ι)
    [K.HasHomology i] : s.homologyCycleSection i ≫ K.iCycles i =
      s.homologyInclusionComponent i := by
  rw [homologyCycleSection, Category.assoc, s.cyclesRetraction_iCycles i]
  change s.homologyInclusionComponent i ≫
    (𝟙 (K.X i) - K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) = _
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    s.homologyInclusionComponent_d i (c.next i), zero_comp, sub_zero]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let rᵢ : Kᵢ → Zᵢ be the
cycles retraction supplied by the normalized splitting. Let tᵢ : Hᵢ → Zᵢ be its
homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. The endomorphism rᵢ ≫ πᵢ ≫
ℓᵢ of Kᵢ equals 1_{Kᵢ} − (Dᵢ + Bᵢ), where Dᵢ = dᵢ,next(i) ≫ s.normalize.hom next(i) i and Bᵢ =
s.normalize.hom i prev(i) ≫ d_prev(i),i are the outgoing and incoming normalized projectors.
-/
theorem Splitting.pointwiseHomologyProjectionInclusion (s : Splitting K) (i : ι)
    [K.HasHomology i] :
    s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := by
  let a : K.X i ⟶ K.X i := dNext i s.normalize.hom
  let b : K.X i ⟶ K.X i := prevD i s.normalize.hom
  have hab : a ≫ b = 0 := by
    change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0
    calc
      _ = K.d i (c.next i) ≫
          (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
            K.d (c.prev i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [s.normalize_hom_comp_hom (c.next i) i (c.prev i)]
        simp only [zero_comp, comp_zero]
  calc
    _ = s.cyclesRetraction i ≫ (K.iCycles i ≫ (𝟙 (K.X i) - b)) := by
      rw [s.homologyπ_homologyInclusionComponent i]
    _ = (𝟙 (K.X i) - a) ≫ (𝟙 (K.X i) - b) := by
      rw [← Category.assoc, s.cyclesRetraction_iCycles i]
    _ = 𝟙 (K.X i) - (a + b) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.id_comp, Category.comp_id, hab]
      abel

section KernelCycles

variable (s : Splitting K) (i : ι) [K.HasHomology i] [HasKernel (K.homologyπ i)]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. The endomorphism 1_{Zᵢ} − πᵢ ≫ tᵢ factors uniquely through kᵢ. Its
factor bᵢ : Zᵢ → Bᵢ is the boundary-kernel projection, characterized by bᵢ ≫ kᵢ = 1_{Zᵢ} − πᵢ
≫ tᵢ.
-/
def Splitting.boundaryKernelProjection : K.cycles i ⟶ kernel (K.homologyπ i) :=
  kernel.lift (K.homologyπ i)
    (𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i) (by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        s.homologyCycleSection_homologyπ i, Category.comp_id, sub_self])

@[reassoc]
theorem Splitting.boundaryKernelProjection_ι :
    s.boundaryKernelProjection i ≫ kernel.ι (K.homologyπ i) =
      𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i :=
  kernel.lift_ι _ _ _

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. For the boundary projection bᵢ defined by bᵢ ≫ kᵢ = 1_{Zᵢ} − πᵢ ≫
tᵢ, the kernel inclusion is a section: kᵢ ≫ bᵢ = 1_{Bᵢ}.
-/
@[reassoc]
theorem Splitting.kernel_ι_boundaryKernelProjection :
    kernel.ι (K.homologyπ i) ≫ s.boundaryKernelProjection i =
      𝟙 (kernel (K.homologyπ i)) := by
  apply (cancel_mono (kernel.ι (K.homologyπ i))).1
  rw [Category.assoc, s.boundaryKernelProjection_ι i]
  simp only [Preadditive.comp_sub, Category.comp_id, kernel.condition_assoc,
    zero_comp, sub_zero, Category.id_comp]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. Let bᵢ : Zᵢ → Bᵢ be the projection with bᵢ ≫ kᵢ = 1_{Zᵢ} − πᵢ ≫ tᵢ.
The homology section has zero boundary coordinate: tᵢ ≫ bᵢ = 0 : Hᵢ → Bᵢ.
-/
@[reassoc]
theorem Splitting.homologyCycleSection_boundaryKernelProjection :
    s.homologyCycleSection i ≫ s.boundaryKernelProjection i = 0 := by
  apply (cancel_mono (kernel.ι (K.homologyπ i))).1
  rw [Category.assoc, s.boundaryKernelProjection_ι i]
  simp only [Preadditive.comp_sub, Category.comp_id,
    s.homologyCycleSection_homologyπ_assoc i,
    sub_self, zero_comp]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its
homology inclusion. Writing bᵢ for the boundary-kernel projection, the endomorphism rᵢ ≫ bᵢ ≫
kᵢ ≫ jᵢ of Kᵢ is exactly s.normalize.hom i prev(i) ≫ d_prev(i),i, the normalized
incoming-boundary projector.
-/
theorem Splitting.boundaryKernelProjection_term :
    s.cyclesRetraction i ≫ s.boundaryKernelProjection i ≫
      kernel.ι (K.homologyπ i) ≫ K.iCycles i = prevD i s.normalize.hom := by
  calc
    _ = s.cyclesRetraction i ≫
        (𝟙 (K.cycles i) - K.homologyπ i ≫ s.homologyCycleSection i) ≫ K.iCycles i := by
      rw [s.boundaryKernelProjection_ι_assoc i]
    _ = s.cyclesRetraction i ≫ K.iCycles i -
          s.cyclesRetraction i ≫ K.homologyπ i ≫ s.homologyInclusionComponent i := by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
        Category.assoc, s.homologyCycleSection_iCycles i]
    _ = (𝟙 (K.X i) - dNext i s.normalize.hom) -
          (𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom)) := by
      rw [s.cyclesRetraction_iCycles i, s.pointwiseHomologyProjectionInclusion i]
    _ = prevD i s.normalize.hom := by abel

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting, and assume
homology at i and a kernel Bᵢ of πᵢ:Zᵢ→Hᵢ. With boundary projection bᵢ:Zᵢ→Bᵢ, kernel inclusion
kᵢ and homology section tᵢ:Hᵢ→Zᵢ, the cycles object is a binary bicone over Bᵢ,Hᵢ: projections
(bᵢ,πᵢ), inclusions (kᵢ,tᵢ), identities kᵢ≫bᵢ=1 and tᵢ≫πᵢ=1, and zero cross-composites.
-/
def Splitting.cyclesBoundaryHomologyBicone :
    BinaryBicone (kernel (K.homologyπ i)) (K.homology i) where
  pt := K.cycles i
  fst := s.boundaryKernelProjection i
  snd := K.homologyπ i
  inl := kernel.ι (K.homologyπ i)
  inr := s.homologyCycleSection i
  inl_fst := s.kernel_ι_boundaryKernelProjection i
  inl_snd := kernel.condition _
  inr_fst := s.homologyCycleSection_boundaryKernelProjection i
  inr_snd := s.homologyCycleSection_homologyπ i

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. The bicone with vertex Zᵢ, projections (bᵢ,πᵢ), and inclusions
(kᵢ,tᵢ) is both a product and a coproduct of Bᵢ and Hᵢ. Thus it is a binary biproduct
decomposition of the cycles.
-/
def Splitting.cyclesBoundaryHomologyBiconeIsBilimit :
    (s.cyclesBoundaryHomologyBicone i).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ (kernelIsKernel (K.homologyπ i))

include s in
/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. The splitting supplies a binary biproduct of the boundary kernel
Bᵢ and Hᵢ, realized by Zᵢ with its boundary/homology projections and kernel/homology-section
inclusions.
-/
theorem Splitting.hasBoundaryHomologyBiproduct :
    HasBinaryBiproduct (kernel (K.homologyπ i)) (K.homology i) :=
  HasBinaryBiproduct.mk {
    bicone := s.cyclesBoundaryHomologyBicone i
    isBilimit := s.cyclesBoundaryHomologyBiconeIsBilimit i }

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. The canonical cycles decomposition is Zᵢ ≅ Bᵢ ⊞ Hᵢ. Its forward
coordinates are the boundary projection bᵢ and the original quotient πᵢ; its inverse includes
Bᵢ by kᵢ and Hᵢ by tᵢ.
-/
def Splitting.cyclesBoundaryHomologyIso :
    letI := s.hasBoundaryHomologyBiproduct i
    K.cycles i ≅ kernel (K.homologyπ i) ⊞ K.homology i := by
  letI := s.hasBoundaryHomologyBiproduct i
  exact biprod.uniqueUpToIso _ _ (s.cyclesBoundaryHomologyBiconeIsBilimit i)

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. For the canonical isomorphism eᵢ : Zᵢ ≅ Bᵢ ⊞ Hᵢ associated to s,
the first coordinate is its boundary projection: eᵢ.hom ≫ biprod.fst =
s.boundaryKernelProjection i.
-/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_hom_fst :
    letI := s.hasBoundaryHomologyBiproduct i
    (s.cyclesBoundaryHomologyIso i).hom ≫ biprod.fst = s.boundaryKernelProjection i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.lift_fst]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. For eᵢ : Zᵢ ≅ Bᵢ ⊞ Hᵢ constructed from s, the second coordinate
is the homology quotient: eᵢ.hom ≫ biprod.snd = πᵢ.
-/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_hom_snd :
    letI := s.hasBoundaryHomologyBiproduct i
    (s.cyclesBoundaryHomologyIso i).hom ≫ biprod.snd = K.homologyπ i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.lift_snd]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. For the cycles decomposition eᵢ : Zᵢ ≅ Bᵢ ⊞ Hᵢ, the inverse
restricted to Bᵢ is exactly its kernel inclusion: biprod.inl ≫ eᵢ.inv = kᵢ.
-/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_inl_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    biprod.inl ≫ (s.cyclesBoundaryHomologyIso i).inv = kernel.ι (K.homologyπ i) := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.inl_desc]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume πᵢ has a kernel Bᵢ
with inclusion kᵢ : Bᵢ → Zᵢ. Let tᵢ : Hᵢ → Zᵢ be its homology-to-cycles section and ℓᵢ : Hᵢ →
Kᵢ its homology inclusion. For the cycles decomposition eᵢ : Zᵢ ≅ Bᵢ ⊞ Hᵢ, the inverse
restricted to Hᵢ is the constructed cycle section: biprod.inr ≫ eᵢ.inv = tᵢ.
-/
@[reassoc]
theorem Splitting.cyclesBoundaryHomologyIso_inr_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    biprod.inr ≫ (s.cyclesBoundaryHomologyIso i).inv = s.homologyCycleSection i := by
  let := s.hasBoundaryHomologyBiproduct i
  dsimp only [cyclesBoundaryHomologyIso, biprod.uniqueUpToIso, cyclesBoundaryHomologyBicone]
  simp only [biprod.inr_desc]

end KernelCycles

section CokernelTerm

variable (s : Splitting K) (i : ι) [K.HasHomology i] [HasCokernel (K.iCycles i)]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. The complementary endomorphism 1_{Kᵢ} − rᵢ ≫ jᵢ annihilates the cycles
inclusion. It descends uniquely through qᵢ to eᵢ : Qᵢ → Kᵢ, characterized by qᵢ ≫ eᵢ = 1_{Kᵢ}
− rᵢ ≫ jᵢ.
-/
def Splitting.outgoingCokernelSection : cokernel (K.iCycles i) ⟶ K.X i :=
  cokernel.desc (K.iCycles i)
    (𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i) (by
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        s.iCycles_cyclesRetraction i, Category.id_comp, sub_self])

@[reassoc]
theorem Splitting.cokernel_π_outgoingCokernelSection :
    cokernel.π (K.iCycles i) ≫ s.outgoingCokernelSection i =
      𝟙 (K.X i) - s.cyclesRetraction i ≫ K.iCycles i :=
  cokernel.π_desc _ _ _

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. For eᵢ : Qᵢ → Kᵢ descended from 1_{Kᵢ} − rᵢ ≫ jᵢ, its composite with the
quotient is eᵢ ≫ qᵢ = 1_{Qᵢ}. Thus the cycles quotient is split.
-/
@[reassoc]
theorem Splitting.outgoingCokernelSection_cokernel_π :
    s.outgoingCokernelSection i ≫ cokernel.π (K.iCycles i) =
      𝟙 (cokernel (K.iCycles i)) := by
  apply (cancel_epi (cokernel.π (K.iCycles i))).1
  rw [← Category.assoc, s.cokernel_π_outgoingCokernelSection i]
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    cokernel.condition, comp_zero, sub_zero, Category.comp_id]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. Let eᵢ : Qᵢ → Kᵢ be the section determined by qᵢ ≫ eᵢ = 1_{Kᵢ} − rᵢ ≫
jᵢ. Its cycles coordinate vanishes: eᵢ ≫ rᵢ = 0 : Qᵢ → Zᵢ.
-/
@[reassoc]
theorem Splitting.outgoingCokernelSection_cyclesRetraction :
    s.outgoingCokernelSection i ≫ s.cyclesRetraction i = 0 := by
  apply (cancel_epi (cokernel.π (K.iCycles i))).1
  rw [← Category.assoc, s.cokernel_π_outgoingCokernelSection i]
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
    s.iCycles_cyclesRetraction i, Category.comp_id, sub_self, comp_zero]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. For the section eᵢ : Qᵢ → Kᵢ determined by the normalized splitting, qᵢ
≫ eᵢ = dᵢ,next(i) ≫ s.normalize.hom next(i) i, the normalized outgoing projector.
-/
theorem Splitting.outgoingCokernelProjectionSection :
    cokernel.π (K.iCycles i) ≫ s.outgoingCokernelSection i =
      dNext i s.normalize.hom := by
  rw [s.cokernel_π_outgoingCokernelSection i, s.cyclesRetraction_iCycles i]
  abel

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. With eᵢ : Qᵢ → Kᵢ the complementary section, Kᵢ forms a binary bicone
over Zᵢ and Qᵢ: projections are rᵢ,qᵢ and inclusions are jᵢ,eᵢ. The diagonal composites are
identities and the cross-composites are zero.
-/
def Splitting.termCyclesOutgoingBicone :
    BinaryBicone (K.cycles i) (cokernel (K.iCycles i)) where
  pt := K.X i
  fst := s.cyclesRetraction i
  snd := cokernel.π (K.iCycles i)
  inl := K.iCycles i
  inr := s.outgoingCokernelSection i
  inl_fst := s.iCycles_cyclesRetraction i
  inl_snd := cokernel.condition _
  inr_fst := s.outgoingCokernelSection_cyclesRetraction i
  inr_snd := s.outgoingCokernelSection_cokernel_π i

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. The bicone with vertex Kᵢ, projections (rᵢ,qᵢ), and inclusions (jᵢ,eᵢ)
is a product and coproduct of Zᵢ and Qᵢ. The cokernel universal property and the splitting
give the binary biproduct.
-/
def Splitting.termCyclesOutgoingBiconeIsBilimit :
    (s.termCyclesOutgoingBicone i).IsBilimit :=
  BinaryBicone.isBilimitOfCokernelSnd _ (cokernelIsCokernel (K.iCycles i))

include s in
/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. The splitting supplies a binary biproduct of Zᵢ and Qᵢ, realized by Kᵢ
with projections rᵢ,qᵢ and complementary inclusions jᵢ,eᵢ.
-/
theorem Splitting.hasCyclesOutgoingBiproduct :
    HasBinaryBiproduct (K.cycles i) (cokernel (K.iCycles i)) :=
  HasBinaryBiproduct.mk {
    bicone := s.termCyclesOutgoingBicone i
    isBilimit := s.termCyclesOutgoingBiconeIsBilimit i }

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. The canonical isomorphism Kᵢ ≅ Zᵢ ⊞ Qᵢ has forward coordinates rᵢ and
qᵢ, and inverse inclusions jᵢ and the complementary section eᵢ : Qᵢ → Kᵢ.
-/
def Splitting.termCyclesOutgoingIso :
    letI := s.hasCyclesOutgoingBiproduct i
    K.X i ≅ K.cycles i ⊞ cokernel (K.iCycles i) := by
  letI := s.hasCyclesOutgoingBiproduct i
  exact biprod.uniqueUpToIso _ _ (s.termCyclesOutgoingBiconeIsBilimit i)

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. For e : Kᵢ ≅ Zᵢ ⊞ Qᵢ furnished by s, its first coordinate is the
normalized cycles retraction: e.hom ≫ biprod.fst = rᵢ.
-/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_hom_fst :
    letI := s.hasCyclesOutgoingBiproduct i
    (s.termCyclesOutgoingIso i).hom ≫ biprod.fst = s.cyclesRetraction i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.lift_fst]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. For the isomorphism e : Kᵢ ≅ Zᵢ ⊞ Qᵢ furnished by s, its second
coordinate is the original cycles quotient: e.hom ≫ biprod.snd = qᵢ.
-/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_hom_snd :
    letI := s.hasCyclesOutgoingBiproduct i
    (s.termCyclesOutgoingIso i).hom ≫ biprod.snd = cokernel.π (K.iCycles i) := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.lift_snd]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. For the term decomposition e : Kᵢ ≅ Zᵢ ⊞ Qᵢ, the inverse
restricted to Zᵢ is the cycles inclusion: biprod.inl ≫ e.inv = jᵢ.
-/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_inl_inv :
    letI := s.hasCyclesOutgoingBiproduct i
    biprod.inl ≫ (s.termCyclesOutgoingIso i).inv = K.iCycles i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.inl_desc]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume jᵢ has a cokernel Qᵢ
with projection qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ be the cycles retraction supplied by the
normalized splitting. For e : Kᵢ ≅ Zᵢ ⊞ Qᵢ, the inverse restricted to Qᵢ is the complementary
section with qᵢ ≫ eᵢ = 1_{Kᵢ} − rᵢ ≫ jᵢ: biprod.inr ≫ e.inv = eᵢ.
-/
@[reassoc]
theorem Splitting.termCyclesOutgoingIso_inr_inv :
    letI := s.hasCyclesOutgoingBiproduct i
    biprod.inr ≫ (s.termCyclesOutgoingIso i).inv = s.outgoingCokernelSection i := by
  let := s.hasCyclesOutgoingBiproduct i
  dsimp only [termCyclesOutgoingIso, biprod.uniqueUpToIso, termCyclesOutgoingBicone]
  simp only [biprod.inr_desc]

end CokernelTerm

section DegreeDecomposition

variable (s : Splitting K) (i : ι) [K.HasHomology i]
  [HasKernel (K.homologyπ i)] [HasCokernel (K.iCycles i)]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. The splitting
constructs Bᵢ ⊞ Hᵢ and then a binary biproduct (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ. These products exist from the
kernel, cokernel and splitting data; no separate global biproduct assumption is made.
-/
theorem Splitting.hasDegreeDecompositionBiproduct :
    letI := s.hasBoundaryHomologyBiproduct i
    HasBinaryBiproduct (kernel (K.homologyπ i) ⊞ K.homology i) (cokernel (K.iCycles i)) := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  exact hasBinaryBiproduct_of_iso (s.cyclesBoundaryHomologyIso i)
    (Iso.refl (cokernel (K.iCycles i)))

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ
be the cycles retraction supplied by the normalized splitting. Let tᵢ : Hᵢ → Zᵢ be its
homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. Combining the cycles and
term decompositions gives Kᵢ ≅ (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ. The three forward coordinates are rᵢ followed
by the boundary projection, rᵢ ≫ πᵢ, and qᵢ. The inverse includes boundaries by kᵢ ≫ jᵢ,
homology by ℓᵢ, and the outgoing quotient by its complementary section.
-/
def Splitting.degreeDecompositionIso :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    K.X i ≅ (kernel (K.homologyπ i) ⊞ K.homology i) ⊞ cokernel (K.iCycles i) := by
  letI := s.hasBoundaryHomologyBiproduct i
  letI := s.hasCyclesOutgoingBiproduct i
  letI := s.hasDegreeDecompositionBiproduct i
  exact s.termCyclesOutgoingIso i ≪≫
    biprod.mapIso (s.cyclesBoundaryHomologyIso i) (Iso.refl (cokernel (K.iCycles i)))

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ
be the cycles retraction supplied by the normalized splitting. For the canonical degree
decomposition e : Kᵢ ≅ (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ, the boundary coordinate is e.hom ≫ biprod.fst ≫
biprod.fst = rᵢ ≫ s.boundaryKernelProjection i.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_boundary :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.fst =
      s.cyclesRetraction i ≫ s.boundaryKernelProjection i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, cyclesBoundaryHomologyIso_hom_fst,
    termCyclesOutgoingIso_hom_fst_assoc]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ
be the cycles retraction supplied by the normalized splitting. For e : Kᵢ ≅ (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ,
the homology coordinate is e.hom ≫ biprod.fst ≫ biprod.snd = rᵢ ≫ πᵢ.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_homology :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.fst ≫ biprod.snd =
      s.cyclesRetraction i ≫ K.homologyπ i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_fst_assoc, cyclesBoundaryHomologyIso_hom_snd,
    termCyclesOutgoingIso_hom_fst_assoc]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. For e : Kᵢ ≅ (Bᵢ
⊞ Hᵢ) ⊞ Qᵢ constructed from s, the outgoing coordinate is e.hom ≫ biprod.snd = qᵢ : Kᵢ → Qᵢ.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_hom_outgoing :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    (s.degreeDecompositionIso i).hom ≫ biprod.snd = cokernel.π (K.iCycles i) := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_hom, biprod.mapIso_hom,
    Category.assoc, biprod.map_snd, Iso.refl_hom, Category.comp_id,
    termCyclesOutgoingIso_hom_snd]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. For the degree
decomposition e : Kᵢ ≅ (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ, the inverse restricted to the boundary coordinate is
biprod.inl ≫ biprod.inl ≫ e.inv = kᵢ ≫ jᵢ : Bᵢ → Kᵢ.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_boundary_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inl ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv =
      kernel.ι (K.homologyπ i) ≫ K.iCycles i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inl_map_assoc, cyclesBoundaryHomologyIso_inl_inv_assoc,
    termCyclesOutgoingIso_inl_inv]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let tᵢ : Hᵢ → Zᵢ
be its homology-to-cycles section and ℓᵢ : Hᵢ → Kᵢ its homology inclusion. For e : Kᵢ ≅ (Bᵢ ⊞
Hᵢ) ⊞ Qᵢ, the inverse restricted to homology is biprod.inr ≫ biprod.inl ≫ e.inv = ℓᵢ : Hᵢ →
Kᵢ, the inclusion constructed from s.normalize.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_homology_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inr ≫ biprod.inl ≫ (s.degreeDecompositionIso i).inv =
      s.homologyInclusionComponent i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inl_map_assoc, cyclesBoundaryHomologyIso_inr_inv_assoc,
    termCyclesOutgoingIso_inl_inv, homologyCycleSection_iCycles]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ = K.cycles i, Hᵢ = K.homology i, jᵢ : Zᵢ → Kᵢ for
the cycle inclusion, and πᵢ : Zᵢ → Hᵢ for the homology quotient. Assume both the kernel Bᵢ of
πᵢ and the cokernel Qᵢ of jᵢ exist, with maps kᵢ : Bᵢ → Zᵢ and qᵢ : Kᵢ → Qᵢ. Let rᵢ : Kᵢ → Zᵢ
be the cycles retraction supplied by the normalized splitting. For the degree decomposition e
: Kᵢ ≅ (Bᵢ ⊞ Hᵢ) ⊞ Qᵢ, the inverse restricted to Qᵢ is biprod.inr ≫ e.inv =
s.outgoingCokernelSection i. This section descends 1_{Kᵢ} − rᵢ ≫ jᵢ through qᵢ.
-/
@[reassoc]
theorem Splitting.degreeDecompositionIso_outgoing_inv :
    letI := s.hasBoundaryHomologyBiproduct i
    letI := s.hasDegreeDecompositionBiproduct i
    biprod.inr ≫ (s.degreeDecompositionIso i).inv = s.outgoingCokernelSection i := by
  let := s.hasBoundaryHomologyBiproduct i
  let := s.hasCyclesOutgoingBiproduct i
  let := s.hasDegreeDecompositionBiproduct i
  simp only [degreeDecompositionIso, Iso.trans_inv, biprod.mapIso_inv,
    biprod.inr_map_assoc, Iso.refl_inv, Category.id_comp,
    termCyclesOutgoingIso_inr_inv]

end DegreeDecomposition

end HomologicalComplex
