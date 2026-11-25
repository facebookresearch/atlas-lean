/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration
public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripConvergence
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLefflerLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.SpectralObject.EpiMono
/-!
# Stable images and the original kernel-filtration graded quotient

Compatible classes in the finite kernel towers lift through the actual
limiting total cone. The chosen-limit projection has the native eventual
image by Mittag--Leffler. This identifies stabilized finite interval images
with the image of the original total restriction kernel, preserving its
literal restriction and quotient maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite
open scoped ZeroObject

universe u v

namespace CategoryTheory.Limits

variable {G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}}

/-- The actual index tail of an original inverse sequence. -/
abbrev stableImageTailIndex (N : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ where
  obj j := op (N + j.unop)
  map f := (homOfLE (Nat.add_le_add_left (leOfHom f.unop) N)).op

/-- The original projections from tail stages back to the same unshifted indices. -/
def stableImageTailProjection (G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (N : ℕ) :
    stableImageTailIndex N ⋙ G ⟶ G where
  app j := G.map (homOfLE (show j.unop ≤ N + j.unop by omega)).op
  naturality i j f := by
    change G.map ((stableImageTailIndex N).map f) ≫
        G.map (homOfLE (show j.unop ≤ N + j.unop by omega)).op =
      G.map (homOfLE (show i.unop ≤ N + i.unop by omega)).op ≫ G.map f
    rw [← G.map_comp, ← G.map_comp] <;> congr 1 <;> subsingleton

/-- The same original total cone restricted to an actual index tail. -/
abbrev stableImageTailCone (c : Cone G) (N : ℕ) : Cone (stableImageTailIndex N ⋙ G) :=
  c.whisker (stableImageTailIndex N)

/-- Extend compatible tail coordinates using the actual earlier-stage restrictions. -/
abbrev stableImageTailConeExtend (N : ℕ) (d : Cone (stableImageTailIndex N ⋙ G)) : Cone G :=
  ⟨d.pt, d.π ≫ stableImageTailProjection G N⟩

/-- Restricting the actual total limiting cone to an index tail preserves
the limiting property and every literal original evaluation. -/
def stableImageTailConeIsLimit (c : Cone G) (hc : IsLimit c) (N : ℕ) :
    IsLimit (stableImageTailCone c N) where
  lift d := hc.lift (stableImageTailConeExtend N d)
  fac d j := by
    change hc.lift (stableImageTailConeExtend N d) ≫ c.π.app (op (N + j.unop)) = d.π.app j
    rw [hc.fac]
    exact d.w ((homOfLE (show j.unop ≤ N + j.unop by omega)).op)
  uniq d m hm := by
    apply hc.hom_ext
    intro j
    let f : op (N + j.unop) ⟶ j := (homOfLE (show j.unop ≤ N + j.unop by omega)).op
    calc
      m ≫ c.π.app j = m ≫ c.π.app (op (N + j.unop)) ≫ G.map f := by rw [c.w f]
      _ = d.π.app j ≫ G.map f := by
        have hj : m ≫ c.π.app (op (N + j.unop)) = d.π.app j := hm j
        rw [← Category.assoc, hj]
      _ = hc.lift (stableImageTailConeExtend N d) ≫ c.π.app j := by rw [hc.fac]; rfl

/-- The actual pointwise kernels of compatible restrictions to a fixed cut. -/
def stableImageKernelTower (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj j := kernel (γ.app j)
  map {i j} f := kernel.map (γ.app i) (γ.app j) (G.map f) (𝟙 M)
    (by simpa using (γ.naturality f).symm)
  map_id j := by
    apply (cancel_mono (kernel.ι (γ.app j))).mp
    simp
  map_comp {i j k} f g := by
    apply (cancel_mono (kernel.ι (γ.app k))).mp
    simp [G.map_comp, Category.assoc]

/-- The original kernel inclusions form an actual natural transformation. -/
def stableImageKernelInclusion (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) :
    stableImageKernelTower γ ⟶ G where
  app j := kernel.ι (γ.app j)
  naturality i j f := by
    exact kernel.lift_ι _ _ _

/-- Restriction of the total cone to the fixed lower cut. -/
def stableImageConeRestriction (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) : c.pt ⟶ M :=
  c.π.app (op 0) ≫ γ.app (op 0)

theorem stableImageCone_lower_eq (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (j : ℕᵒᵖ) : c.π.app j ≫ γ.app j = stableImageConeRestriction γ c := by
  let f : j ⟶ op 0 := (homOfLE (Nat.zero_le j.unop)).op
  have hγ : G.map f ≫ γ.app (op 0) = γ.app j := by simpa using γ.naturality f
  rw [← hγ, ← Category.assoc, c.w f]
  rfl

/-- The original total restriction kernel, with its compatible maps to all
actual finite-stage kernels. -/
def stableImageKernelCone (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) :
    Cone (stableImageKernelTower γ) where
  pt := kernel (stableImageConeRestriction γ c)
  π :=
    { app := fun j => kernel.lift (γ.app j)
        (kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app j) (by
          rw [Category.assoc, stableImageCone_lower_eq]
          exact kernel.condition _)
      naturality := by
        intro i j f
        apply (cancel_mono (kernel.ι (γ.app j))).mp
        simp only [Functor.const_obj_map, Category.id_comp, Category.assoc,
          stableImageKernelTower, kernel.map, kernel.lift_ι_assoc, kernel.lift_ι]
        rw [c.w f]
        simp }

@[reassoc]
theorem stableImageKernelCone_π_ι (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (j : ℕᵒᵖ) :
    (stableImageKernelCone γ c).π.app j ≫ kernel.ι (γ.app j) =
      kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app j :=
  kernel.lift_ι _ _ _

/-- Forget the kernel conditions while retaining the same original cone coordinates. -/
def stableImageKernelConeForget (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (d : Cone (stableImageKernelTower γ)) : Cone G :=
  ⟨d.pt, d.π ≫ stableImageKernelInclusion γ⟩

/-- A compatible kernel cone lifts through the actual total limit and then
through the original total restriction kernel. -/
def stableImageKernelConeLift (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) :
    d.pt ⟶ (stableImageKernelCone γ c).pt :=
  kernel.lift (stableImageConeRestriction γ c)
    (hc.lift (stableImageKernelConeForget γ d)) (by
      unfold stableImageConeRestriction
      rw [← Category.assoc, hc.fac]
      change (d.π.app (op 0) ≫ kernel.ι (γ.app (op 0))) ≫ γ.app (op 0) = 0
      simp only [Category.assoc, kernel.condition, comp_zero])

@[reassoc]
theorem stableImageKernelConeLift_ι (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) :
    stableImageKernelConeLift γ c hc d ≫ kernel.ι (stableImageConeRestriction γ c) =
      hc.lift (stableImageKernelConeForget γ d) :=
  kernel.lift_ι _ _ _

theorem stableImageKernelConeLift_fac (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) (j : ℕᵒᵖ) :
    stableImageKernelConeLift γ c hc d ≫ (stableImageKernelCone γ c).π.app j = d.π.app j := by
  apply (cancel_mono (kernel.ι (γ.app j))).mp
  rw [Category.assoc, stableImageKernelCone_π_ι, ← Category.assoc,
    stableImageKernelConeLift_ι, hc.fac]
  rfl

/-- The original total restriction kernel is the actual limit of the finite
kernel tower. Only the original total-cone limit is supplied. -/
def stableImageKernelConeIsLimit (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) : IsLimit (stableImageKernelCone γ c) where
  lift := stableImageKernelConeLift γ c hc
  fac := stableImageKernelConeLift_fac γ c hc
  uniq d m hm := by
    apply (cancel_mono (kernel.ι (stableImageConeRestriction γ c))).mp
    apply hc.hom_ext
    intro j
    calc
      (m ≫ kernel.ι (stableImageConeRestriction γ c)) ≫ c.π.app j =
        m ≫ (stableImageKernelCone γ c).π.app j ≫ kernel.ι (γ.app j) := by
          rw [Category.assoc, ← stableImageKernelCone_π_ι, ← Category.assoc]
      _ = d.π.app j ≫ kernel.ι (γ.app j) := by rw [← Category.assoc, hm]
      _ = (stableImageKernelConeLift γ c hc d ≫ kernel.ι (stableImageConeRestriction γ c)) ≫
          c.π.app j := by
        rw [stableImageKernelConeLift_ι, hc.fac]
        rfl

/-- The original total kernel and the actual chosen kernel-tower limit. -/
def stableImageKernelLimitIso (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) :
    kernel (stableImageConeRestriction γ c) ≅ limit (stableImageKernelTower γ) :=
  (stableImageKernelConeIsLimit γ c hc).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
theorem stableImageKernelLimitIso_hom_π (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (j : ℕᵒᵖ) :
    (stableImageKernelLimitIso γ c hc).hom ≫ limit.π (stableImageKernelTower γ) j =
      (stableImageKernelCone γ c).π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The actual evaluation of the original total restriction kernel. -/
def stableImageKernelConeEdge (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) :
    kernel (stableImageConeRestriction γ c) ⟶ G.obj (op 0) :=
  kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app (op 0)

theorem stableImageRange_comp_of_epi {A B D : AddCommGrpCat.{u}}
    (e : A ⟶ B) [Epi e] (f : B ⟶ D) : Set.range (e ≫ f) = Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance x
    exact ⟨z, rfl⟩

theorem stableImageRange_postcomp_eq {A B D Q : AddCommGrpCat.{u}}
    (f : A ⟶ D) (g : B ⟶ D) (t : D ⟶ Q) (h : Set.range f = Set.range g) :
    Set.range (f ≫ t) = Set.range (g ≫ t) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ : f x ∈ Set.range g := h ▸ Set.mem_range_self x
    refine ⟨z, ?_⟩
    exact congrArg t hz
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ : g x ∈ Set.range f := h.symm ▸ Set.mem_range_self x
    refine ⟨z, ?_⟩
    exact congrArg t hz

theorem stableImageKernelEdge_range_congr {A M Q : AddCommGrpCat.{u}}
    (f g : A ⟶ M) (t : A ⟶ Q) (h : f = g) :
    Set.range (kernel.ι f ≫ t) = Set.range (kernel.ι g ≫ t) := by
  cases h
  rfl

/-- Mittag--Leffler and an attained actual kernel image identify the
original total-kernel evaluation with that finite-stage evaluation. -/
theorem stableImageKernelConeEdge_range
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) (hc : IsLimit c)
    (hML : (stableImageKernelTower γ).IsSequentialMittagLeffler) (R : ℕ)
    (hR : ((stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op)) :
    Set.range (stableImageKernelConeEdge γ c) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op ≫
        kernel.ι (γ.app (op 0))) := by
  have hπ : Set.range (limit.π (stableImageKernelTower γ) (op 0)) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op) :=
    (Concrete.range_limit_π_eq_eventualRange_of_isMittagLeffler _ hML 0).trans hR
  have hfac : (stableImageKernelLimitIso γ c hc).hom ≫
      (limit.π (stableImageKernelTower γ) (op 0) ≫ kernel.ι (γ.app (op 0))) =
        stableImageKernelConeEdge γ c := by
    rw [← Category.assoc, stableImageKernelLimitIso_hom_π, stableImageKernelCone_π_ι]
    rfl
  rw [← hfac, stableImageRange_comp_of_epi]
  exact stableImageRange_postcomp_eq _ _ _ hπ

/-- Existing Mittag--Leffler gives an attained actual kernel image at
every sufficiently late index. -/
theorem stableImageKernelTower_attainedRange
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (hML : (stableImageKernelTower γ).IsSequentialMittagLeffler) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      ((stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
        Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op) := by
  let U := (stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}
  obtain ⟨j, f, hf⟩ := U.isMittagLeffler_iff_eventualRange.mp hML (op 0)
  refine ⟨j.unop, fun R hR => ?_⟩
  change U.eventualRange (op 0) = Set.range (U.map (homOfLE (Nat.zero_le R)).op)
  have h := U.eventualRange_eq_range_precomp ((homOfLE hR).op) f hf
  have he : (homOfLE hR).op ≫ f = (homOfLE (Nat.zero_le R)).op := Subsingleton.elim _ _
  simpa only [he] using h

/-- Finite actual stage groups earn Mittag--Leffler for their actual
restriction kernels through the existing finite-image criterion. -/
theorem stableImageKernelTower_isMittagLeffler_of_finite
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (hFinite : ∀ j : ℕᵒᵖ, _root_.Finite (G.obj j)) :
    (stableImageKernelTower γ).IsSequentialMittagLeffler := by
  let U := (stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}
  apply U.isMittagLeffler_of_exists_finite_range
  intro j
  letI : _root_.Finite (G.obj j) := hFinite j
  letI : _root_.Finite ((stableImageKernelTower γ).obj j) :=
    _root_.Finite.of_injective (kernel.ι (γ.app j))
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
  letI : _root_.Finite (U.obj j) := by
    change _root_.Finite (kernel (γ.app j) : AddCommGrpCat.{u})
    exact _root_.Finite.of_injective (kernel.ι (γ.app j))
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
  exact ⟨j, 𝟙 _, Set.toFinite _⟩

end CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type v} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (S : SpectralObject AddCommGrpCat.{u} ι)

/-- The actual absolute interval above a cut. -/
def stableImageRightObject (n : ℤ) (i : ι) : AddCommGrpCat.{u} :=
  (S.H n).obj (mk₁ (stableIntervalRight i))

/-- The original restriction between two absolute cut intervals. -/
def stableImageRightMap (n : ℤ) {i j : ι} (hij : i ≤ j) :
    stableImageRightObject S n i ⟶ stableImageRightObject S n j :=
  (S.H n).map (twoδ₁Toδ₀ (homOfLE hij) (stableIntervalRight j)
    (stableIntervalRight i) (by subsingleton))

-- Keep the original bounded-order parameter in this compatibility declaration.
@[simp, nolint unusedArguments]
theorem stableImageRightMap_id (n : ℤ) (i : ι) :
    stableImageRightMap S n (le_refl i) = 𝟙 (stableImageRightObject S n i) := by
  dsimp only [stableImageRightMap]
  have h : twoδ₁Toδ₀ (homOfLE (le_refl i)) (stableIntervalRight i)
      (stableIntervalRight i) (by subsingleton) = 𝟙 (mk₁ (stableIntervalRight i)) := Subsingleton.elim _ _
  rw [h, (S.H n).map_id]
  rfl

-- Keep the original bounded-order parameter in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stableImageRightMap_comp (n : ℤ) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    stableImageRightMap S n hij ≫ stableImageRightMap S n hjk =
      stableImageRightMap S n (hij.trans hjk) := by
  dsimp only [stableImageRightMap]
  rw [← (S.H n).map_comp] <;> congr 1 <;> subsingleton

/-- The native window with the actual top endpoint. -/
def stableImagePageWindow (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    AddCommGrpCat.{u} :=
  S.E (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1)

/-- The native window embeds into the original absolute middle-cut group. -/
def stableImagePageWindowToRight (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    stableImagePageWindow S n h₀₁ h₁₂ ⟶ stableImageRightObject S n i₁ :=
  S.ιE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1) ≫
    S.fromOpcycles (homOfLE h₁₂) (stableIntervalRight i₂) (stableIntervalRight i₁) (by subsingleton) n

instance stableImagePageWindowToRight_mono (n : ℤ) {i₀ i₁ i₂ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) : Mono (stableImagePageWindowToRight S n h₀₁ h₁₂) := by
  dsimp only [stableImagePageWindowToRight]
  infer_instance

/-- Actual relative classes map onto the native window. -/
def stableImagePageWindowFromRelative (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    (S.H n).obj (mk₁ (homOfLE (h₀₁.trans h₁₂))) ⟶ stableImagePageWindow S n h₀₁ h₁₂ :=
  S.toCycles (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE (h₀₁.trans h₁₂)) (by subsingleton) n ≫
    S.πE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1)

instance stableImagePageWindowFromRelative_epi (n : ℤ) {i₀ i₁ i₂ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) : Epi (stableImagePageWindowFromRelative S n h₀₁ h₁₂) := by
  dsimp only [stableImagePageWindowFromRelative]
  infer_instance

/-- The original triple LES whose image is the finite absolute restriction kernel. -/
def stableImageIntervalKernelSequence (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    ShortComplex AddCommGrpCat.{u} :=
  S.sc₂ (homOfLE h₀₂) (stableIntervalRight i₂) (stableIntervalRight i₀) (by subsingleton) n

/-- Actual relative classes cover the original absolute restriction kernel. -/
def stableImageIntervalKernelLift (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    (S.H n).obj (mk₁ (homOfLE h₀₂)) ⟶ kernel (stableImageRightMap S n h₀₂) :=
  (stableImageIntervalKernelSequence S n h₀₂).toCycles ≫
    (stableImageIntervalKernelSequence S n h₀₂).cyclesIsoKernel.hom

instance stableImageIntervalKernelLift_epi (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    Epi (stableImageIntervalKernelLift S n h₀₂) := by
  letI : Epi (stableImageIntervalKernelSequence S n h₀₂).toCycles :=
    (S.exact₂ (homOfLE h₀₂) (stableIntervalRight i₂) (stableIntervalRight i₀) (by subsingleton) n).epi_toCycles
  dsimp only [stableImageIntervalKernelLift]
  infer_instance

-- Keep the original bounded-order parameter in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stableImageIntervalKernelLift_ι (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    stableImageIntervalKernelLift S n h₀₂ ≫ kernel.ι (stableImageRightMap S n h₀₂) =
      (stableImageIntervalKernelSequence S n h₀₂).f := by
  dsimp only [stableImageIntervalKernelLift]
  change (stableImageIntervalKernelSequence S n h₀₂).toCycles ≫
      (stableImageIntervalKernelSequence S n h₀₂).cyclesIsoKernel.hom ≫
        kernel.ι (stableImageIntervalKernelSequence S n h₀₂).g = _
  simp only [Category.assoc, ShortComplex.cyclesIsoKernel, kernel.lift_ι, ShortComplex.toCycles_i]

/-- Both original relative-class maps give the same absolute restriction. -/
theorem stableImagePageWindowFromRelative_comp_right
    (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    stableImagePageWindowFromRelative S n h₀₁ h₁₂ ≫ stableImagePageWindowToRight S n h₀₁ h₁₂ =
      stableImageIntervalKernelLift S n (h₀₁.trans h₁₂) ≫
        (kernel.ι (stableImageRightMap S n (h₀₁.trans h₁₂)) ≫ stableImageRightMap S n h₀₁) := by
  have hπ := S.πE_ιE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂)
    (n - 1) n (n + 1) (by omega) (by omega)
  have hπ' := congrArg (fun t => t ≫
    S.fromOpcycles (homOfLE h₁₂) (stableIntervalRight i₂) (stableIntervalRight i₁)
      (by subsingleton) n) hπ
  simp only [Category.assoc] at hπ'
  dsimp only [stableImagePageWindowFromRelative, stableImagePageWindowToRight]
  simp only [Category.assoc]
  rw [hπ', S.toCycles_i_assoc, S.p_fromOpcycles, stableImageIntervalKernelLift_ι_assoc]
  change (S.H n).map (twoδ₁Toδ₀ (homOfLE h₀₁) (homOfLE h₁₂)
      (homOfLE (h₀₁.trans h₁₂)) (by subsingleton)) ≫
      (S.H n).map (twoδ₂Toδ₁ (homOfLE h₁₂) (stableIntervalRight i₂)
        (stableIntervalRight i₁) (by subsingleton)) =
    (S.H n).map (twoδ₂Toδ₁ (homOfLE (h₀₁.trans h₁₂)) (stableIntervalRight i₂)
      (stableIntervalRight i₀) (by subsingleton)) ≫ stableImageRightMap S n h₀₁
  dsimp only [stableImageRightMap]
  rw [← (S.H n).map_comp, ← (S.H n).map_comp] <;> congr 1 <;> subsingleton

/-- A native finite window has the image of the actual finite restriction
kernel, by the original triple LES and original edge maps. -/
theorem stableImagePageWindowToRight_range
    (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    Set.range (stableImagePageWindowToRight S n h₀₁ h₁₂) =
      Set.range (kernel.ι (stableImageRightMap S n (h₀₁.trans h₁₂)) ≫ stableImageRightMap S n h₀₁) := by
  rw [← stableImageRange_comp_of_epi (stableImagePageWindowFromRelative S n h₀₁ h₁₂),
    stableImagePageWindowFromRelative_comp_right, stableImageRange_comp_of_epi]

/-- The original absolute cut intervals on an antitone sequence of finite left cuts. -/
def stableImageRightTower (n : ℤ) (a : ℕ → ι) (ha : Antitone a) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj j := stableImageRightObject S n (a j.unop)
  map f := stableImageRightMap S n (ha (leOfHom f.unop))
  map_id j := stableImageRightMap_id S n (a j.unop)
  map_comp f g := (stableImageRightMap_comp S n _ _).symm

/-- Literal restriction of every absolute finite interval to the fixed lower cut. -/
def stableImageTowerRestriction (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) :
    stableImageRightTower S n a ha ⟶ (Functor.const ℕᵒᵖ).obj (stableImageRightObject S n c) where
  app j := stableImageRightMap S n ((ha (Nat.zero_le j.unop)).trans hc)
  naturality i j f := by
    change stableImageRightMap S n (ha (leOfHom f.unop)) ≫
        stableImageRightMap S n ((ha (Nat.zero_le j.unop)).trans hc) =
      stableImageRightMap S n ((ha (Nat.zero_le i.unop)).trans hc) ≫ 𝟙 _
    rw [stableImageRightMap_comp, Category.comp_id]

/-- The actual full-endpoint total group with its original restriction coordinates. -/
def stableImageTotalCone (n : ℤ) (a : ℕ → ι) (ha : Antitone a) :
    Cone (stableImageRightTower S n a ha) where
  pt := stableImageRightObject S n (⊥ : ι)
  π :=
    { app := fun j => stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a j.unop)
      naturality := by
        intro i j f
        change 𝟙 _ ≫ stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a j.unop) =
          stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a i.unop) ≫
            stableImageRightMap S n (ha (leOfHom f.unop))
        rw [Category.id_comp, stableImageRightMap_comp] }

theorem stableImageTotalCone_restriction (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) :
    stableImageConeRestriction (stableImageTowerRestriction S n a ha c hc)
        (stableImageTotalCone S n a ha) =
      stableImageRightMap S n (bot_le : (⊥ : ι) ≤ c) :=
  stableImageRightMap_comp S n _ _

/-- The original stable-cut to finite-window map. Only the left endpoint changes. -/
def stableImagePageComparison (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    stableImagePageWindow S n (bot_le : (⊥ : ι) ≤ a 0) hc ⟶
      stableImagePageWindow S n (ha (Nat.zero_le R)) hc :=
  S.map (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c)
    (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
    (homMk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a R)) (𝟙 (a 0)) (𝟙 c) (𝟙 (⊤ : ι))
      (by subsingleton) (by subsingleton) (by subsingleton))
    (n - 1) n (n + 1) (by omega) (by omega)

@[reassoc]
theorem stableImagePageComparison_comp_right (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    stableImagePageComparison S n a ha c hc R ≫
        stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc =
      stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc := by
  let α : mk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c) ⟶
      mk₃ (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c) :=
    homMk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a R)) (𝟙 (a 0)) (𝟙 c) (𝟙 (⊤ : ι))
      (by subsingleton) (by subsingleton) (by subsingleton)
  have hmap := S.map_ιE (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c)
    (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c) α
    (𝟙 (mk₂ (homOfLE hc) (stableIntervalRight c))) (n - 1) n (n + 1)
    (by subsingleton) (by omega) (by omega)
  simp only [S.opcyclesMap_id, Category.comp_id] at hmap
  simpa only [α, stableImagePageComparison, stableImagePageWindow, stableImagePageWindowToRight,
    stableImageRightObject, Category.assoc] using
    congrArg (fun t => t ≫ S.fromOpcycles (homOfLE hc) (stableIntervalRight c)
      (stableIntervalRight (a 0)) (by subsingleton) n) hmap

instance stableImagePageComparison_mono (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) : Mono (stableImagePageComparison S n a ha c hc R) :=
  mono_of_mono_fac (stableImagePageComparison_comp_right S n a ha c hc R)

/-- The stable endpoint window has the image of the original total kernel. -/
theorem stableImageStableWindow_range
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c) :
    Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) =
      Set.range (stableImageKernelConeEdge (stableImageTowerRestriction S n a ha c hc)
        (stableImageTotalCone S n a ha)) := by
  rw [stableImagePageWindowToRight_range]
  have h := stableImageKernelEdge_range_congr
    (stableImageConeRestriction (stableImageTowerRestriction S n a ha c hc) (stableImageTotalCone S n a ha))
    (stableImageRightMap S n (bot_le : (⊥ : ι) ≤ c))
    (stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a 0))
    (stableImageTotalCone_restriction S n a ha c hc)
  exact h.symm

/-- The finite window has the image of the corresponding actual kernel-tower map. -/
theorem stableImageFiniteWindow_range
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    Set.range (stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
          (homOfLE (Nat.zero_le R)).op ≫
        kernel.ι ((stableImageTowerRestriction S n a ha c hc).app (op 0))) := by
  rw [stableImagePageWindowToRight_range]
  have h := (stableImageKernelInclusion (stableImageTowerRestriction S n a ha c hc)).naturality
    ((homOfLE (Nat.zero_le R)).op)
  exact (congrArg (fun f :
    (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).obj (op R) ⟶
      stableImageRightObject S n (a 0) => Set.range f) h).symm

/-- Actual total-limit lifting and attained kernel images earn an
isomorphism on the original stable-cut to finite-window map. -/
theorem stableImagePageComparison_isIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    IsIso (stableImagePageComparison S n a ha c hc R) := by
  have hRange : Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) =
      Set.range (stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) :=
    (stableImageStableWindow_range S n a ha c hc).trans
      ((stableImageKernelConeEdge_range _ _ hTotal hML R hR).trans
        (stableImageFiniteWindow_range S n a ha c hc R).symm)
  have hSurj : Function.Surjective (stableImagePageComparison S n a ha c hc R) := by
    intro y
    obtain ⟨x, hx⟩ : stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc y ∈
        Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) :=
      hRange.symm ▸ Set.mem_range_self y
    refine ⟨x, ?_⟩
    apply ((AddCommGrpCat.mono_iff_injective (stableImagePageWindowToRight S n
      (ha (Nat.zero_le R)) hc)).mp inferInstance)
    change (stableImagePageComparison S n a ha c hc R ≫
      stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) x = _
    rw [stableImagePageComparison_comp_right]
    exact hx
  letI : Epi (stableImagePageComparison S n a ha c hc R) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hSurj
  exact isIso_of_mono_of_epi _

/-- Finite original stage groups and the actual total limit earn the
stable-cut/window comparison for every sufficiently late finite left cut. -/
theorem stableImagePageComparison_eventually_isIso_of_finite
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hFinite : ∀ j : ℕᵒᵖ, _root_.Finite ((stableImageRightTower S n a ha).obj j)) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R → IsIso (stableImagePageComparison S n a ha c hc R) := by
  have hML := stableImageKernelTower_isMittagLeffler_of_finite
    (stableImageTowerRestriction S n a ha c hc) hFinite
  obtain ⟨N, hN⟩ := stableImageKernelTower_attainedRange (stableImageTowerRestriction S n a ha c hc) hML
  exact ⟨N, fun R hR => stableImagePageComparison_isIso S n a ha c hc hTotal hML R (hN R hR)⟩

/-- A stabilized native window is canonically the graded piece of the
original total restriction-kernel filtration. -/
def stableImageKernelGradedIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    stableImagePageWindow S n (ha (Nat.zero_le R)) hc ≅ S.stableIntervalKernelGraded n hc := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotal hML R hR
  exact (asIso (stableImagePageComparison S n a ha c hc R)).symm ≪≫ S.stableIntervalKernelGradedIso n hc

@[reassoc]
theorem stableImageKernelGradedIso_comparison
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    stableImagePageComparison S n a ha c hc R ≫
        (stableImageKernelGradedIso S n a ha c hc hTotal hML R hR).hom =
      (S.stableIntervalKernelGradedIso n hc).hom := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotal hML R hR
  simp only [stableImageKernelGradedIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- A native finite right endpoint is padded by its actual indexing map;
only the already earned omitted-right interval zero is required. -/
def stableImageFiniteWindowKernelGradedIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (d : ι) (hcd : c ≤ d)
    (hRight : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d)))) :
    S.E (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (n - 1) n (n + 1) (by omega) (by omega) ≅ S.stableIntervalKernelGraded n hc :=
  S.isoMapFourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1) hRight (by omega) (by omega) ≪≫
      stableImageKernelGradedIso S n a ha c hc hTotal hML R hR

/-- Equality of literal indexing cuts transports only the native window. -/
def stableImageWindowEqIso (n : ℤ) {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : j₀ ≤ j₁) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃)
    (e₀ : i₀ = j₀) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) (e₃ : i₃ = j₃) :
    S.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) (n - 1) n (n + 1) ≅
      S.E (homOfLE h₀₁') (homOfLE h₁₂') (homOfLE h₂₃') (n - 1) n (n + 1) := by
  subst j₀ j₁ j₂ j₃
  exact Iso.refl _

/-- Identify stable interval kernel graded objects after equality of their two endpoints. -/
def stableImageKernelGradedEqIso (n : ℤ) {i₁ i₂ j₁ j₂ : ι}
    (h : i₁ ≤ i₂) (h' : j₁ ≤ j₂) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) :
    S.stableIntervalKernelGraded n h ≅ S.stableIntervalKernelGraded n h' := by
  subst j₁ j₂
  exact Iso.refl _

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

variable (S : SpectralObject AddCommGrpCat.{u} EInt)

/-- The actual integer left cuts of successive page windows at column `p`. -/
def stableImageSkeletalLeftCuts (p : ℤ) (k : ℕ) : EInt := ((-(p + 1) - (k : ℤ) : ℤ) : EInt)

theorem stableImageSkeletalLeftCuts_antitone (p : ℤ) : Antitone (stableImageSkeletalLeftCuts p) := by
  intro i j hij
  simp [stableImageSkeletalLeftCuts]
  omega

theorem stableImageSkeletal_middle (p : ℤ) : stableImageSkeletalLeftCuts p 0 ≤ ((-p : ℤ) : EInt) := by
  simp [stableImageSkeletalLeftCuts]

/-- The original native skeletal page is the graded original kernel
filtration once the actual kernel image has stabilized. -/
def stableImageSkeletalPageGradedIso (p q : ℤ)
    (hTotal : IsLimit (stableImageTotalCone S (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le R)).op))
    (hRight : IsZero ((S.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt)))))) :
    ((S.skeletalSpectralSequence).page ((R : ℤ) + 1) (by omega)).X (p, q) ≅
      S.skeletalAbutmentGraded (p + q) p := by
  let r : ℤ := (R : ℤ) + 1
  let a := stableImageSkeletalLeftCuts p
  let ha := stableImageSkeletalLeftCuts_antitone p
  let c : EInt := ((-p : ℤ) : EInt)
  let hc := stableImageSkeletal_middle p
  let d : EInt := ((-p + (R : ℤ) : ℤ) : EInt)
  have hcd : c ≤ d := by simp [c, d]
  let he : S.E
      (homOfLE (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; dsimp [r]; omega))
      (homOfLE (show ((-(p + 1) : ℤ) : EInt) ≤ c by simp [c]))
      (homOfLE (show c ≤ ((-p + r - 1 : ℤ) : EInt) by simp [c]; dsimp [r]; omega))
      (p + q - 1) (p + q) (p + q + 1) ≅
      S.E (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (p + q - 1) (p + q) (p + q + 1) :=
    stableImageWindowEqIso S (p + q) _ _ _ _ _ _
      (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
      (by simp [a, stableImageSkeletalLeftCuts]) rfl
      (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d, r]; omega)
  let egrade : S.stableIntervalKernelGraded (p + q) hc ≅ S.skeletalAbutmentGraded (p + q) p :=
    stableImageKernelGradedEqIso S (p + q) hc
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (by simp [a, stableImageSkeletalLeftCuts]) rfl
  exact S.skeletalPageWindowIso r (by dsimp [r]; omega) p q ≪≫ he ≪≫
    stableImageFiniteWindowKernelGradedIso S (p + q) a ha c hc hTotal hML R hR
      d hcd hRight ≪≫ egrade

end CategoryTheory.Abelian.SpectralObject


end
