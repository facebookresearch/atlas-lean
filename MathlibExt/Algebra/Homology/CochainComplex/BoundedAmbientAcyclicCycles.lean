/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTopKernel
public import MathlibExt.CategoryTheory.ExactCategory.KernelOfEpiLift

/-!
# Original source cycles of ambient-acyclic bounded cochains

The original cochain and explicit support window are retained. Ambient
exactness earns each mapped quotient epimorphism; the original image kernel
closure and fully faithful embedding then earn the source cycles, their
original inclusions and quotient maps, and the actual admissible kernel rows.
The construction uses the single canonical `KernelOfEpiLift` family.

All source and ambient object and Hom universes remain independent. Source
homology and global source kernels are absent. The source cycle dictionary
uses the specified exact embedding, conflation reflection and original
kernel-of-epimorphism image closure. No comparison outcome is an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientCycles

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Actual source cycle data at one original integer degree. -/
structure CycleData (K : Bounded E) (j : ℤ) where
  /-- The source object representing the original ambient cycles. -/
  Z : E
  /-- Its actual original inclusion into the cochain term. -/
  ι : Z ⟶ K.obj.X j
  /-- The original incoming differential maps onto these cycles. -/
  q : K.obj.X (j - 1) ⟶ Z
  /-- The same original incoming differential is retained. -/
  factor : q ≫ ι = K.obj.d (j - 1) j
  /-- The inclusion is killed by the original outgoing differential. -/
  zero : ι ≫ K.obj.d j (j + 1) = 0
  /-- The actual mapped quotient is epic. -/
  mappedEpi : Epi (F.map q)
  /-- The mapped inclusion is the kernel of the same original outgoing differential. -/
  mappedIsLimit : IsLimit (KernelFork.ofι (f := F.map (K.obj.d j (j + 1)))
    (F.map ι) (by rw [← F.map_comp, zero, F.map_zero]))

variable (K : Bounded E) (a b : ℤ)
variable (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
variable (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)

/-- At the explicit original top endpoint the actual cycle object is the original top term. -/
def topData : CycleData F K b := by
  have hd : K.obj.d b (b + 1) = 0 :=
    (hSupport (b + 1) (Or.inr (by omega))).eq_of_tgt _ _
  refine
    { Z := K.obj.X b
      ι := 𝟙 _
      q := K.obj.d (b - 1) b
      factor := Category.comp_id _
      zero := by simpa only [Category.id_comp] using hd
      mappedEpi := mappedDifferential_epi_of_acyclic_of_isZero_succ F K b
        (hSupport (b + 1) (Or.inr (by omega))) hK
      mappedIsLimit := ?_ }
  have hMapped : F.map (K.obj.d b (b + 1)) = 0 := by rw [hd, F.map_zero]
  simpa only [F.map_id] using KernelFork.IsLimit.ofId (F.map (K.obj.d b (b + 1))) hMapped

variable [F.Full] [F.Faithful]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

namespace CycleData

variable {F K} {j : ℤ}

/-- Transport the original cycle data only along an equality of original integer indices. -/
def castIndex {k : ℤ} (e : j = k) (D : CycleData F K j) : CycleData F K k := e ▸ D

/-- The actual kernel of the earned mapped quotient uses the canonical original family. -/
def quotientKernelLift (D : CycleData F K j) : Functor.KernelLift F D.q := by
  let _ := D.mappedEpi
  exact F.kernelLiftOfEpi hKernelClosure D.q

/-- Descend one actual degree, retaining the two same original differentials. -/
def predecessor (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CycleData F K (j - 1) := by
  let lift := quotientKernelLift hKernelClosure D
  let _ : Mono (F.map D.ι) := Fork.IsLimit.mono D.mappedIsLimit
  let dHigh := K.obj.d (j - 1 - 1) (j - 1)
  let dLow := K.obj.d (j - 1) j
  have hzero : lift.ι ≫ dLow = 0 := by
    dsimp only [dLow]
    rw [← D.factor, ← Category.assoc, lift.zero, zero_comp]
  have hfactorMap : F.map dLow = F.map D.q ≫ F.map D.ι := by
    dsimp only [dLow]
    rw [← F.map_comp, D.factor]
  let hKernel : IsLimit (KernelFork.ofι (f := F.map dLow) (F.map lift.ι)
      (by rw [← F.map_comp, hzero, F.map_zero])) :=
    isKernelCompMono lift.mappedIsLimit (F.map D.ι) hfactorMap
  have hdd : F.map dHigh ≫ F.map dLow = 0 := by
    rw [← F.map_comp]
    change F.map (K.obj.d (j - 1 - 1) (j - 1) ≫ K.obj.d (j - 1) j) = 0
    rw [K.obj.d_comp_d, F.map_zero]
  let l := KernelFork.IsLimit.lift' hKernel (F.map dHigh) hdd
  let qNext : K.obj.X (j - 1 - 1) ⟶ lift.K := F.preimage l.1
  have hmapqNext : F.map qNext = l.1 := F.map_preimage _
  have hfactor : qNext ≫ lift.ι = dHigh := by
    apply F.map_injective
    rw [F.map_comp, hmapqNext]
    simpa only [KernelFork.ι_ofι] using l.2
  let M := (F.mapHomologicalComplex (.up ℤ)).obj K.obj
  let S : ShortComplex A := ShortComplex.mk (F.map dHigh) (F.map dLow) hdd
  have hExact : S.Exact := by
    have h := (M.exactAt_iff' (j - 1 - 1) (j - 1) j (by simp) (by simp)).mp
      (hAcyclic (j - 1))
    let e : M.sc' (j - 1 - 1) (j - 1) j ≅ S :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 _ ≫ F.map dHigh = F.map dHigh ≫ 𝟙 _; simp)
        (by change 𝟙 _ ≫ F.map dLow = F.map dLow ≫ 𝟙 _; simp)
    exact ShortComplex.exact_of_iso e h
  let _ : Epi (kernel.lift (F.map dLow) (F.map dHigh) hdd) :=
    S.exact_iff_epi_kernel_lift.mp hExact
  let e : F.obj lift.K ≅ kernel (F.map dLow) :=
    hKernel.conePointUniqueUpToIso
      (t := KernelFork.ofι (kernel.ι (F.map dLow)) (kernel.condition (F.map dLow)))
      (kernelIsKernel (F.map dLow))
  have he := IsLimit.conePointUniqueUpToIso_hom_comp hKernel
    (kernelIsKernel (F.map dLow)) WalkingParallelPair.zero
  have he' : e.hom ≫ kernel.ι (F.map dLow) = F.map lift.ι := he
  have hlCanonical : l.1 ≫ e.hom = kernel.lift (F.map dLow) (F.map dHigh) hdd := by
    apply (cancel_mono (kernel.ι (F.map dLow))).mp
    rw [Category.assoc, he']
    have hl : l.1 ≫ F.map lift.ι = F.map dHigh := by
      simpa only [KernelFork.ι_ofι] using l.2
    rw [hl, kernel.lift_ι]
  have hlEq : l.1 = kernel.lift (F.map dLow) (F.map dHigh) hdd ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    rw [hlCanonical, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hlEpi : Epi l.1 := by
    rw [hlEq]
    infer_instance
  have hqEpi : Epi (F.map qNext) := by rw [hmapqNext]; exact hlEpi
  exact
    { Z := lift.K
      ι := lift.ι
      q := qNext
      factor := hfactor
      zero := by
        rw [sub_add_cancel]
        exact hzero
      mappedEpi := hqEpi
      mappedIsLimit := KernelFork.isLimitOfIsLimitOfIff' hKernel
        (F.map (K.obj.d (j - 1) (j - 1 + 1))) (by
          intro W φ
          have h (k : ℤ) (hk : k = j) :
              φ ≫ F.map (K.obj.d (j - 1) j) = 0 ↔
                φ ≫ F.map (K.obj.d (j - 1) k) = 0 := by
            subst k
            rfl
          exact h _ (by omega)) }

/-- The new source cycle is the same actual represented kernel of the preceding quotient. -/
theorem predecessor_Z (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (predecessor hKernelClosure D hAcyclic).Z = (quotientKernelLift hKernelClosure D).K := rfl

/-- The complete new cycle inclusion is the same original canonical kernel inclusion. -/
theorem predecessor_ι (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (predecessor hKernelClosure D hAcyclic).ι = (quotientKernelLift hKernelClosure D).ι := rfl

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- The actual new inclusion and old quotient form the original admissible source kernel row. -/
theorem predecessor_row_isAdmissibleExact (D : CycleData F K j) :
    IsAdmissibleExact (quotientKernelLift hKernelClosure D).shortComplex := by
  let _ := D.mappedEpi
  exact (quotientKernelLift hKernelClosure D).isAdmissibleExact

end CycleData

/-- The original explicit endpoint is decreased by one at every successor. -/
def degree (b : ℤ) : ℕ → ℤ := Nat.rec b (fun _ j => j - 1)

/-- The recursive endpoint is exactly the original endpoint minus the natural step count. -/
theorem degree_eq (b : ℤ) (n : ℕ) : degree b n = b - (n : ℤ) := by
  induction n with
  | zero => simp only [degree, Nat.rec_zero, Nat.cast_zero, sub_zero]
  | succ n ih =>
    change degree b n - 1 = b - (↑(n + 1) : ℤ)
    rw [ih]
    omega

/-- Earn source cycle data throughout descent from the same original explicit support endpoint. -/
def boundary : (n : ℕ) → CycleData F K (degree b n) :=
  Nat.rec (topData F K a b hSupport hK)
    (fun _ D => D.predecessor hKernelClosure hK)

/-- The whole top source cycle is the unchanged original top-term construction. -/
theorem boundary_zero : boundary F K a b hSupport hK hKernelClosure 0 =
    topData F K a b hSupport hK := rfl

/-- Each whole successor is the original earned kernel descent on the same complex. -/
theorem boundary_succ (n : ℕ) :
    boundary F K a b hSupport hK hKernelClosure (n + 1) =
      (boundary F K a b hSupport hK hKernelClosure n).predecessor hKernelClosure hK := rfl

/-- The original explicit descent reaches every original degree at or below its upper endpoint. -/
theorem degree_toNat (b j : ℤ) (hj : j ≤ b) : degree b (b - j).toNat = j := by
  rw [degree_eq]
  omega

/-- Original cycle data in every integer degree, with the actual zero terms above the window. -/
def dataAt (j : ℤ) : CycleData F K j := by
  by_cases hj : j ≤ b
  · exact CycleData.castIndex (degree_toNat b j hj)
      (boundary F K a b hSupport hK hKernelClosure (b - j).toNat)
  · exact topData F K a j (fun k hk => hSupport k (by omega)) hK

/-- The original outgoing quotient is the incoming quotient of the next original cycle data. -/
def outgoing (j : ℤ) : K.obj.X j ⟶ (dataAt F K a b hSupport hK hKernelClosure (j + 1)).Z :=
  eqToHom (congrArg K.obj.X (show j = (j + 1) - 1 by omega)) ≫
    (dataAt F K a b hSupport hK hKernelClosure (j + 1)).q

/-- Both original row maps factor the same literal outgoing cochain differential. -/
theorem outgoing_factor (j : ℤ) :
    outgoing F K a b hSupport hK hKernelClosure j ≫
      (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι = K.obj.d j (j + 1) := by
  rw [outgoing, Category.assoc,
    (dataAt F K a b hSupport hK hKernelClosure (j + 1)).factor]
  have h (i : ℤ) (hi : i = j) :
      eqToHom (congrArg K.obj.X hi.symm) ≫ K.obj.d i (j + 1) = K.obj.d j (j + 1) := by
    subst i
    simp
  exact h _ (by omega)

/-- The actual mapped outgoing quotient is epic in every original integer degree. -/
theorem outgoing_map_epi (j : ℤ) : Epi (F.map (outgoing F K a b hSupport hK hKernelClosure j)) := by
  let _ := (dataAt F K a b hSupport hK hKernelClosure (j + 1)).mappedEpi
  rw [outgoing, F.map_comp]
  infer_instance

/-- The original cycle inclusion is monic, by its actual mapped kernel and faithfulness. -/
theorem inclusion_mono (j : ℤ) :
    Mono (dataAt F K a b hSupport hK hKernelClosure j).ι :=
  F.mono_of_mono_map
    (Fork.IsLimit.mono (dataAt F K a b hSupport hK hKernelClosure j).mappedIsLimit)

/-- The two same original row maps have zero composite. -/
theorem row_zero (j : ℤ) :
    (dataAt F K a b hSupport hK hKernelClosure j).ι ≫
      outgoing F K a b hSupport hK hKernelClosure j = 0 := by
  let _ := inclusion_mono F K a b hSupport hK hKernelClosure (j + 1)
  apply (cancel_mono (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι).mp
  rw [zero_comp, Category.assoc, outgoing_factor]
  exact (dataAt F K a b hSupport hK hKernelClosure j).zero

/-- The actual original cycle/inclusion/quotient row in every original integer degree. -/
abbrev row (j : ℤ) : ShortComplex E :=
  ShortComplex.mk (dataAt F K a b hSupport hK hKernelClosure j).ι
    (outgoing F K a b hSupport hK hKernelClosure j)
    (row_zero F K a b hSupport hK hKernelClosure j)

/-- The actual mapped cycle inclusion is the kernel of the original mapped quotient. -/
def mappedRowIsLimit (j : ℤ) :
    IsLimit (KernelFork.ofι (f := F.map (outgoing F K a b hSupport hK hKernelClosure j))
      (F.map (dataAt F K a b hSupport hK hKernelClosure j).ι) (by
        rw [← F.map_comp, row_zero, F.map_zero])) := by
  have hzero : F.map (dataAt F K a b hSupport hK hKernelClosure j).ι ≫
      F.map (outgoing F K a b hSupport hK hKernelClosure j) = 0 := by
    rw [← F.map_comp, row_zero, F.map_zero]
  have hfactor : F.map (outgoing F K a b hSupport hK hKernelClosure j) ≫
      F.map (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι =
      F.map (K.obj.d j (j + 1)) := by
    rw [← F.map_comp, outgoing_factor]
  exact isKernelOfComp
    (f := F.map (outgoing F K a b hSupport hK hKernelClosure j))
    (F.map (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι)
    (F.map (K.obj.d j (j + 1)))
    (dataAt F K a b hSupport hK hKernelClosure j).mappedIsLimit hzero hfactor

/-- Every actual source cycle row maps to a short exact row in the ambient abelian category. -/
theorem row_map_shortExact (j : ℤ) :
    ((row F K a b hSupport hK hKernelClosure j).map F).ShortExact := by
  let hKernel := mappedRowIsLimit F K a b hSupport hK hKernelClosure j
  have hExact : ((row F K a b hSupport hK hKernelClosure j).map F).Exact :=
    ((row F K a b hSupport hK hKernelClosure j).map F).exact_of_f_is_kernel hKernel
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKernel)
    (outgoing_map_epi F K a b hSupport hK hKernelClosure j)

/-- The source cycle objects are zero outside the same original geometric support window. -/
theorem cycles_isZero_outside (j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (dataAt F K a b hSupport hK hKernelClosure j).Z := by
  let _ := inclusion_mono F K a b hSupport hK hKernelClosure j
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (dataAt F K a b hSupport hK hKernelClosure j).ι).mp
  simp only [Category.id_comp, zero_comp]
  exact (hSupport j hj).eq_of_tgt _ _

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Reflection of the same actual ambient row earns the original source conflation in every degree. -/
theorem row_isAdmissibleExact (j : ℤ) :
    IsAdmissibleExact (row F K a b hSupport hK hKernelClosure j) :=
  F.reflects_admissibleExact _ (row_map_shortExact F K a b hSupport hK hKernelClosure j)

/-- Each original source cycle row has its actual source kernel universal property. -/
def rowIsLimit (j : ℤ) :
    IsLimit (KernelFork.ofι (f := outgoing F K a b hSupport hK hKernelClosure j)
      (dataAt F K a b hSupport hK hKernelClosure j).ι
      (row_zero F K a b hSupport hK hKernelClosure j)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (row_isAdmissibleExact F K a b hSupport hK hKernelClosure j)

/-- Each same original source quotient has its actual source cokernel universal property. -/
def rowIsColimit (j : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (f := (dataAt F K a b hSupport hK hKernelClosure j).ι)
      (outgoing F K a b hSupport hK hKernelClosure j)
      (row_zero F K a b hSupport hK hKernelClosure j)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact
    (row_isAdmissibleExact F K a b hSupport hK hKernelClosure j)

/-- Original all-integer admissible cycle data on the same original bounded cochain. -/
structure AdmissibleAcyclicData (K : Bounded E) where
  /-- The source cycle objects in all original integer degrees. -/
  Z : ℤ → E
  /-- The actual original cycle inclusions. -/
  ι : ∀ j, Z j ⟶ K.obj.X j
  /-- The actual original outgoing quotients. -/
  q : ∀ j, K.obj.X j ⟶ Z (j + 1)
  /-- The actual original row composites are zero. -/
  zero : ∀ j, ι j ≫ q j = 0
  /-- The actual original source rows are admissible exact. -/
  admissible : ∀ j, IsAdmissibleExact (ShortComplex.mk (ι j) (q j) (zero j))
  /-- Both original row maps factor the same literal cochain differentials. -/
  factor : ∀ j, q j ≫ ι (j + 1) = K.obj.d j (j + 1)

/-- The original ambient-acyclic complex earns all original source cycle conflations. -/
def admissibleData : AdmissibleAcyclicData K where
  Z j := (dataAt F K a b hSupport hK hKernelClosure j).Z
  ι j := (dataAt F K a b hSupport hK hKernelClosure j).ι
  q j := outgoing F K a b hSupport hK hKernelClosure j
  zero := row_zero F K a b hSupport hK hKernelClosure
  admissible := row_isAdmissibleExact F K a b hSupport hK hKernelClosure
  factor := outgoing_factor F K a b hSupport hK hKernelClosure

section Converse

variable (G : E ⥤ A) [G.Additive] [G.IsExact]

/-- Exact preservation sends the original admissible cycle rows to ambient acyclicity. -/
theorem ambient_acyclic_of_admissibleData (D : AdmissibleAcyclicData K) :
    ((G.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic := by
  let M := (G.mapHomologicalComplex (.up ℤ)).obj K.obj
  have hAt (j : ℤ) : M.ExactAt (j + 1) := by
    let R : ShortComplex E := ShortComplex.mk (D.ι (j + 1)) (D.q (j + 1)) (D.zero (j + 1))
    have hR : (R.map G).ShortExact := G.map_admissibleExact R (D.admissible (j + 1))
    have hPrev : ((ShortComplex.mk (D.ι j) (D.q j) (D.zero j)).map G).ShortExact :=
      G.map_admissibleExact _ (D.admissible j)
    let _ : Epi (G.map (D.q j)) := hPrev.epi_g
    have hzeroE : K.obj.d j (j + 1) ≫ D.q (j + 1) = 0 := by
      rw [← D.factor j, Category.assoc, D.zero (j + 1), comp_zero]
    have hzero : G.map (K.obj.d j (j + 1)) ≫ G.map (D.q (j + 1)) = 0 := by
      rw [← G.map_comp, hzeroE, G.map_zero]
    let S : ShortComplex A :=
      ShortComplex.mk (G.map (K.obj.d j (j + 1))) (G.map (D.q (j + 1))) hzero
    let φ : S ⟶ R.map G :=
      { τ₁ := G.map (D.q j)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change G.map (D.q j) ≫ G.map (D.ι (j + 1)) =
            G.map (K.obj.d j (j + 1)) ≫ 𝟙 _
          rw [Category.comp_id, ← G.map_comp, D.factor j]
        comm₂₃ := by
          change 𝟙 _ ≫ G.map (D.q (j + 1)) = G.map (D.q (j + 1)) ≫ 𝟙 _
          simp }
    have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hR.exact
    have hNext : ((ShortComplex.mk (D.ι (j + 1 + 1)) (D.q (j + 1 + 1))
        (D.zero (j + 1 + 1))).map G).ShortExact :=
      G.map_admissibleExact _ (D.admissible (j + 1 + 1))
    let _ : Mono (G.map (D.ι (j + 1 + 1))) := hNext.mono_f
    let ψ : S ⟶ M.sc' j (j + 1) (j + 1 + 1) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := G.map (D.ι (j + 1 + 1))
        comm₁₂ := by
          change 𝟙 _ ≫ G.map (K.obj.d j (j + 1)) =
            G.map (K.obj.d j (j + 1)) ≫ 𝟙 _
          simp
        comm₂₃ := by
          change 𝟙 _ ≫ G.map (K.obj.d (j + 1) (j + 1 + 1)) =
            G.map (D.q (j + 1)) ≫ G.map (D.ι (j + 1 + 1))
          rw [Category.id_comp, ← G.map_comp, D.factor (j + 1)] }
    have hExact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hS
    exact (M.exactAt_iff' j (j + 1) (j + 1 + 1) (by simp) (by simp)).mpr hExact
  intro j
  simpa only [sub_add_cancel] using hAt (j - 1)

end Converse

variable [F.IsExact]

include hKernelClosure in
/-- The original bounded ambient acyclicity is exactly the original all-degree cycle conflation data. -/
theorem ambient_acyclic_iff_admissibleData :
    ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic ↔
      Nonempty (AdmissibleAcyclicData K) := by
  constructor
  · intro hAcyclic
    obtain ⟨a', b', hWindow⟩ := K.property
    exact ⟨admissibleData F K a' b' hWindow hAcyclic hKernelClosure⟩
  · rintro ⟨D⟩
    exact ambient_acyclic_of_admissibleData K F D

end CochainComplex.Bounded.AmbientCycles

end
