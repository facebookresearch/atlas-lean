/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Degree-zero Roos cohomology and limits

For a coefficient diagram with a limit, its limit cone is the kernel of the
degree-zero Roos differential. The universal lift is characterized by the
limit projections and the zero-chain coordinates. The degree-zero homology
comparison identifies Roos cohomology with this limit, naturally in the
coefficient diagram. The kernel construction uses preadditivity, sized
products and the indicated diagram limit.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Preadditive A]
  [HasProducts.{max u₁ v₁} A]

/-- The signed zero-degree differential on the edge representing a diagram arrow. -/
theorem roosComplex_d_zero_π_mk₁ (M : I ⥤ A) {i j : I} (f : i ⟶ j) :
    (roosComplex M).d 0 1 ≫ roosπ M (ComposableArrows.mk₁ f.op) =
      roosπ M (ComposableArrows.mk₀ (op i)) ≫ M.map f -
        (show (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj j from
          roosπ M (ComposableArrows.mk₀ (op j))) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial M).obj (SimplexCategory.mk 1)
  let d : X₀ ⟶ X₁ := (roosComplex M).d 0 1
  let F : ComposableArrows Iᵒᵖ 1 := ComposableArrows.mk₁ f.op
  let q : X₁ ⟶ M.obj j := roosπ M F
  let pᵢ : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
  let pⱼ : X₀ ⟶ M.obj j := roosπ M (ComposableArrows.mk₀ (op j))
  let q₀ : X₀ ⟶ M.obj i := roosπ M ((nerve Iᵒᵖ).δ 0 F)
  let q₁ : X₀ ⟶ M.obj j := roosπ M ((nerve Iᵒᵖ).δ 1 F)
  let b : M.obj j ⟶ M.obj j := M.map ((faceLeftHom (1 : Fin 2) F).unop)
  have e₀ : (nerve Iᵒᵖ).δ 0 F = ComposableArrows.mk₀ (op i) :=
    ComposableArrows.ext₀ rfl
  have e₁ : (nerve Iᵒᵖ).δ 1 F = ComposableArrows.mk₀ (op j) :=
    ComposableArrows.ext₀ rfl
  have hπ : ∀ {F₀ F₁ : ComposableArrows Iᵒᵖ 0}, F₀ = F₁ →
      HEq (roosπ M F₀) (roosπ M F₁) := by
    intro F₀ F₁ h
    cases h
    rfl
  have hp₀ : q₀ = pᵢ := eq_of_heq (hπ e₀)
  have hp₁ : q₁ = pⱼ := eq_of_heq (hπ e₁)
  have hbF : (faceLeftHom (1 : Fin 2) F : op j ⟶ op j) = 𝟙 (op j) := by
    change F.map (𝟙 (0 : Fin 2)) = 𝟙 (op j)
    exact F.map_id _
  have hbop : ((faceLeftHom (1 : Fin 2) F).unop : j ⟶ j) = 𝟙 j :=
    congrArg (fun k : op j ⟶ op j => k.unop) hbF
  have hb : b = 𝟙 (M.obj j) :=
    (congrArg (fun k : j ⟶ j => M.map k) hbop).trans (M.map_id j)
  have hd : d ≫ q = q₀ ≫ M.map f - q₁ ≫ b := roosComplex_d_zero_π M F
  change d ≫ q = pᵢ ≫ M.map f - pⱼ
  exact hd.trans (by rw [hp₀, hp₁, hb, Category.comp_id])

/-- A zero-degree Roos cycle satisfies the diagram compatibility equations. -/
theorem roos_cycle_π_naturality (M : I ⥤ A) {Z : A}
    (u : Z ⟶ (roosComplex M).X 0) (hu : u ≫ (roosComplex M).d 0 1 = 0)
    {i j : I} (f : i ⟶ j) :
    u ≫ roosπ M (ComposableArrows.mk₀ (op i)) ≫ M.map f =
      u ≫ roosπ M (ComposableArrows.mk₀ (op j)) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial M).obj (SimplexCategory.mk 1)
  let u₀ : Z ⟶ X₀ := u
  let d : X₀ ⟶ X₁ := (roosComplex M).d 0 1
  let q : X₁ ⟶ M.obj j := roosπ M (ComposableArrows.mk₁ f.op)
  let pᵢ : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
  let pⱼ : X₀ ⟶ M.obj j := roosπ M (ComposableArrows.mk₀ (op j))
  have hu₀ : u₀ ≫ d = 0 := hu
  have hd : d ≫ q = pᵢ ≫ M.map f - pⱼ := roosComplex_d_zero_π_mk₁ M f
  have h : (u₀ ≫ pᵢ) ≫ M.map f - u₀ ≫ pⱼ = 0 := by
    calc
      (u₀ ≫ pᵢ) ≫ M.map f - u₀ ≫ pⱼ = u₀ ≫ (pᵢ ≫ M.map f - pⱼ) := by
        rw [Preadditive.comp_sub, Category.assoc]
      _ = u₀ ≫ (d ≫ q) := congrArg (fun k => u₀ ≫ k) hd.symm
      _ = (u₀ ≫ d) ≫ q := (Category.assoc u₀ d q).symm
      _ = 0 ≫ q := congrArg (fun k : Z ⟶ X₁ => k ≫ q) hu₀
      _ = 0 := zero_comp
  change u₀ ≫ pᵢ ≫ M.map f = u₀ ≫ pⱼ
  exact (Category.assoc u₀ pᵢ (M.map f)).symm.trans (sub_eq_zero.mp h)

/-- The diagram cone associated to a degree-zero Roos cycle. -/
def roosConeOfCycle (M : I ⥤ A) {Z : A}
    (u : Z ⟶ (roosComplex M).X 0) (hu : u ≫ (roosComplex M).d 0 1 = 0) :
    Cone M where
  pt := Z
  π :=
    { app := fun i ↦
        (show Z ⟶ (roosCosimplicial M).obj (SimplexCategory.mk 0) from u) ≫
          roosπ M (ComposableArrows.mk₀ (op i))
      naturality i j f := by
        let u₀ : Z ⟶ (roosCosimplicial M).obj (SimplexCategory.mk 0) := u
        let pᵢ : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj i :=
          roosπ M (ComposableArrows.mk₀ (op i))
        let pⱼ : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj j :=
          roosπ M (ComposableArrows.mk₀ (op j))
        change 𝟙 Z ≫ (u₀ ≫ pⱼ) = (u₀ ≫ pᵢ) ≫ M.map f
        exact (Category.id_comp (u₀ ≫ pⱼ)).trans
          ((roos_cycle_π_naturality M u hu f).symm.trans
            (Category.assoc u₀ pᵢ (M.map f)).symm) }

/-- The cone has exactly the supplied cycle's source as its point. -/
@[simp]
theorem roosConeOfCycle_pt (M : I ⥤ A) {Z : A}
    (u : Z ⟶ (roosComplex M).X 0) (hu : u ≫ (roosComplex M).d 0 1 = 0) :
    (roosConeOfCycle M u hu).pt = Z := rfl

/-- The cone projection is the zero-word coefficient of the supplied cycle. -/
@[simp]
theorem roosConeOfCycle_π_app (M : I ⥤ A) {Z : A}
    (u : Z ⟶ (roosComplex M).X 0) (hu : u ≫ (roosComplex M).d 0 1 = 0) (i : I) :
    (roosConeOfCycle M u hu).π.app i =
      u ≫ roosπ M (ComposableArrows.mk₀ (op i)) := rfl

section IndividualLimit

variable (M : I ⥤ A) [HasLimit M]

/-- The limit family included in the zero-degree Roos object. -/
def roosLimitToZero : limit M ⟶ (roosComplex M).X 0 :=
  Pi.lift (fun F : ComposableArrows Iᵒᵖ 0 ↦ limit.π M (F.left.unop)) ≫
    (roosObjIso M 0).inv

/-- Every zero-word projection is the corresponding limit projection. -/
@[reassoc (attr := simp)]
theorem roosLimitToZero_π (F : ComposableArrows Iᵒᵖ 0) :
    roosLimitToZero M ≫ roosπ M F = limit.π M (F.left.unop) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let P₀ : A := ∏ᶜ (roosFamily M 0)
  let e : X₀ ≅ P₀ := roosObjIso M 0
  let t : limit M ⟶ P₀ :=
    Pi.lift (fun F : ComposableArrows Iᵒᵖ 0 ↦ limit.π M F.left.unop)
  let p : P₀ ⟶ M.obj F.left.unop := Pi.π (roosFamily M 0) F
  let q : X₀ ⟶ M.obj F.left.unop := roosπ M F
  have hq : e.hom ≫ p = q := roosObjIso_hom_π M F
  have hInv : e.inv ≫ q = p := by
    calc
      e.inv ≫ q = e.inv ≫ (e.hom ≫ p) := congrArg (fun k => e.inv ≫ k) hq.symm
      _ = (e.inv ≫ e.hom) ≫ p := (Category.assoc e.inv e.hom p).symm
      _ = 𝟙 P₀ ≫ p := congrArg (fun k : P₀ ⟶ P₀ => k ≫ p) e.inv_hom_id
      _ = p := Category.id_comp p
  change (t ≫ e.inv) ≫ q = limit.π M F.left.unop
  calc
    (t ≫ e.inv) ≫ q = t ≫ (e.inv ≫ q) := Category.assoc t e.inv q
    _ = t ≫ p := congrArg (fun k => t ≫ k) hInv
    _ = limit.π M F.left.unop :=
      Pi.lift_comp_π (f := roosFamily M 0)
        (fun F : ComposableArrows Iᵒᵖ 0 ↦ limit.π M F.left.unop) F

/-- The limit inclusion is annihilated by the zero-degree differential. -/
@[reassoc]
theorem roosLimitToZero_d_zero :
    roosLimitToZero M ≫ (roosComplex M).d 0 1 = 0 := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial M).obj (SimplexCategory.mk 1)
  let l : limit M ⟶ X₀ := roosLimitToZero M
  let d : X₀ ⟶ X₁ := (roosComplex M).d 0 1
  change l ≫ d = 0
  apply roos_hom_ext M (n := 1)
  intro F
  obtain ⟨i, j, f, rfl⟩ := ComposableArrows.mk₁_surjective F
  let q : X₁ ⟶ M.obj i.unop := roosπ M (ComposableArrows.mk₁ f)
  let pᵢ : X₀ ⟶ M.obj i.unop := roosπ M (ComposableArrows.mk₀ i)
  let pⱼ : X₀ ⟶ M.obj j.unop := roosπ M (ComposableArrows.mk₀ j)
  have hd : d ≫ q = pⱼ ≫ M.map f.unop - pᵢ :=
    roosComplex_d_zero_π_mk₁ M f.unop
  have hlᵢ : l ≫ pᵢ = limit.π M i.unop :=
    roosLimitToZero_π M (ComposableArrows.mk₀ i)
  have hlⱼ : l ≫ pⱼ = limit.π M j.unop :=
    roosLimitToZero_π M (ComposableArrows.mk₀ j)
  have hz : (l ≫ d) ≫ q = 0 := by
    calc
      (l ≫ d) ≫ q = l ≫ (d ≫ q) := Category.assoc l d q
      _ = l ≫ (pⱼ ≫ M.map f.unop - pᵢ) := congrArg (fun k => l ≫ k) hd
      _ = (l ≫ pⱼ) ≫ M.map f.unop - l ≫ pᵢ := by
        rw [Preadditive.comp_sub, Category.assoc]
      _ = limit.π M j.unop ≫ M.map f.unop - limit.π M i.unop := by rw [hlᵢ, hlⱼ]
      _ = 0 := sub_eq_zero.mpr (limit.w M f.unop)
  change (l ≫ d) ≫ q = 0 ≫ q
  exact hz.trans (zero_comp).symm

/-- The zero-degree differential fork whose point is the `limit M`. -/
def roosKernelFork : KernelFork ((roosComplex M).d 0 1) :=
  KernelFork.ofι (roosLimitToZero M) (roosLimitToZero_d_zero M)

/-- The cone lift, typed at the source of the supplied cycle. -/
def roosCycleLimitLift {Z : A} (u : Z ⟶ (roosComplex M).X 0)
    (hu : u ≫ (roosComplex M).d 0 1 = 0) : Z ⟶ limit M :=
  limit.lift M (roosConeOfCycle M u hu)

/-- The typed cone lift has precisely the given cycle's coefficients. -/
@[reassoc]
theorem roosCycleLimitLift_π {Z : A} (u : Z ⟶ (roosComplex M).X 0)
    (hu : u ≫ (roosComplex M).d 0 1 = 0) (i : I) :
    roosCycleLimitLift M u hu ≫ limit.π M i =
      u ≫ roosπ M (ComposableArrows.mk₀ (op i)) := by
  change limit.lift M (roosConeOfCycle M u hu) ≫ limit.π M i =
    (roosConeOfCycle M u hu).π.app i
  exact limit.lift_π (roosConeOfCycle M u hu) i

/-- The limit cone is the kernel of the zero-degree differential. -/
def roosKernelForkIsLimit : IsLimit (roosKernelFork M) := by
  refine KernelFork.IsLimit.ofι (roosLimitToZero M) (roosLimitToZero_d_zero M)
    (fun {Z} u hu ↦ roosCycleLimitLift M u hu) ?_ ?_
  · intro Z u hu
    let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
    let u₀ : Z ⟶ X₀ := u
    let l : limit M ⟶ X₀ := roosLimitToZero M
    let v : Z ⟶ limit M := roosCycleLimitLift M u hu
    change v ≫ l = u₀
    apply roos_hom_ext M (n := 0)
    intro F
    obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective F
    let p : X₀ ⟶ M.obj i.unop := roosπ M (ComposableArrows.mk₀ i)
    have hl : l ≫ p = limit.π M i.unop :=
      roosLimitToZero_π M (ComposableArrows.mk₀ i)
    have hv : v ≫ limit.π M i.unop = u₀ ≫ p :=
      roosCycleLimitLift_π M u hu i.unop
    change (v ≫ l) ≫ p = u₀ ≫ p
    exact (Category.assoc v l p).trans ((congrArg (fun k => v ≫ k) hl).trans hv)
  · intro Z u hu m hm
    let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
    let u₀ : Z ⟶ X₀ := u
    let l : limit M ⟶ X₀ := roosLimitToZero M
    let v : Z ⟶ limit M := roosCycleLimitLift M u hu
    apply limit.hom_ext
    intro i
    let p : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
    have hl : l ≫ p = limit.π M i := roosLimitToZero_π M (ComposableArrows.mk₀ (op i))
    have hv : v ≫ limit.π M i = u₀ ≫ p := roosCycleLimitLift_π M u hu i
    have hm' : (m ≫ l) ≫ p = u₀ ≫ p :=
      congrArg (fun k : Z ⟶ X₀ => k ≫ p) hm
    change m ≫ limit.π M i = v ≫ limit.π M i
    calc
      m ≫ limit.π M i = m ≫ (l ≫ p) := congrArg (fun k => m ≫ k) hl.symm
      _ = (m ≫ l) ≫ p := (Category.assoc m l p).symm
      _ = u₀ ≫ p := hm'
      _ = v ≫ limit.π M i := hv.symm

end IndividualLimit

/-- Coefficient maps commute with the limit inclusions. -/
theorem roosLimitToZero_naturality {M N : I ⥤ A} [HasLimit M] [HasLimit N]
    (α : M ⟶ N) :
    limMap α ≫ roosLimitToZero N =
      roosLimitToZero M ≫ ((roosComplexFunctor (I := I) (A := A)).map α).f 0 := by
  let X_M : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let X_N : A := (roosCosimplicial N).obj (SimplexCategory.mk 0)
  let l_M : limit M ⟶ X_M := roosLimitToZero M
  let l_N : limit N ⟶ X_N := roosLimitToZero N
  let r : X_M ⟶ X_N := (roosMap α).app (SimplexCategory.mk 0)
  change limMap α ≫ l_N = l_M ≫ r
  apply roos_hom_ext N (n := 0)
  intro F
  let p_M : X_M ⟶ M.obj F.left.unop := roosπ M F
  let p_N : X_N ⟶ N.obj F.left.unop := roosπ N F
  let c : M.obj F.left.unop ⟶ N.obj F.left.unop := α.app F.left.unop
  have hM : l_M ≫ p_M = limit.π M F.left.unop := roosLimitToZero_π M F
  have hN : l_N ≫ p_N = limit.π N F.left.unop := roosLimitToZero_π N F
  have hr : r ≫ p_N = p_M ≫ c := roosMap_app_π α F
  change (limMap α ≫ l_N) ≫ p_N = (l_M ≫ r) ≫ p_N
  calc
    (limMap α ≫ l_N) ≫ p_N = limMap α ≫ (l_N ≫ p_N) := Category.assoc _ _ _
    _ = limMap α ≫ limit.π N F.left.unop := congrArg (fun k => limMap α ≫ k) hN
    _ = limit.π M F.left.unop ≫ c := limMap_π α F.left.unop
    _ = (l_M ≫ p_M) ≫ c := congrArg (fun k => k ≫ c) hM.symm
    _ = l_M ≫ (p_M ≫ c) := Category.assoc _ _ _
    _ = l_M ≫ (r ≫ p_N) := congrArg (fun k => l_M ≫ k) hr.symm
    _ = (l_M ≫ r) ≫ p_N := (Category.assoc _ _ _).symm

section Homology

variable (M : I ⥤ A) [HasLimit M] [(roosComplex M).HasHomology 0]

/-- Native cycles are identified with the diagram limit through their kernel cones. -/
def roosCyclesLimitIso : (roosComplex M).cycles 0 ≅ limit M :=
  IsLimit.conePointUniqueUpToIso
    ((roosComplex M).cyclesIsKernel 0 1 (by simp)) (roosKernelForkIsLimit M)

/-- The cycles-limit comparison retains the cycle inclusion. -/
theorem roosCyclesLimitIso_hom_lift :
    (roosCyclesLimitIso M).hom ≫ roosLimitToZero M = (roosComplex M).iCycles 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The cycles-limit comparison is characterized on limit projections. -/
@[reassoc]
theorem roosCyclesLimitIso_hom_π (i : I) :
    (roosCyclesLimitIso M).hom ≫ limit.π M i =
      (roosComplex M).iCycles 0 ≫ roosπ M (ComposableArrows.mk₀ (op i)) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let c : (roosComplex M).cycles 0 ⟶ limit M := (roosCyclesLimitIso M).hom
  let l : limit M ⟶ X₀ := roosLimitToZero M
  let z : (roosComplex M).cycles 0 ⟶ X₀ := (roosComplex M).iCycles 0
  let p : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
  have hl : l ≫ p = limit.π M i := roosLimitToZero_π M (ComposableArrows.mk₀ (op i))
  have hc : c ≫ l = z := roosCyclesLimitIso_hom_lift M
  change c ≫ limit.π M i = z ≫ p
  calc
    c ≫ limit.π M i = c ≫ (l ≫ p) := congrArg (fun k => c ≫ k) hl.symm
    _ = (c ≫ l) ≫ p := (Category.assoc c l p).symm
    _ = z ≫ p := congrArg (fun k => k ≫ p) hc

/-- The zero-degree Roos homology is the limit of its coefficients. -/
def roosHomologyZeroIso : (roosComplex M).homology 0 ≅ limit M :=
  (roosComplex M).isoHomologyπ₀.symm ≪≫ roosCyclesLimitIso M

/-- The homology comparison uses the inverse class map and kernel comparison. -/
@[simp]
theorem roosHomologyZeroIso_hom :
    (roosHomologyZeroIso M).hom =
      (roosComplex M).isoHomologyπ₀.inv ≫ (roosCyclesLimitIso M).hom := rfl

/-- The forward comparison is characterized by the limit projections. -/
@[reassoc]
theorem roosHomologyZeroIso_hom_π (i : I) :
    (roosHomologyZeroIso M).hom ≫ limit.π M i =
      (roosComplex M).isoHomologyπ₀.inv ≫ (roosComplex M).iCycles 0 ≫
        roosπ M (ComposableArrows.mk₀ (op i)) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let h : (roosComplex M).homology 0 ⟶ (roosComplex M).cycles 0 :=
    (roosComplex M).isoHomologyπ₀.inv
  let c : (roosComplex M).cycles 0 ⟶ limit M := (roosCyclesLimitIso M).hom
  let z : (roosComplex M).cycles 0 ⟶ X₀ := (roosComplex M).iCycles 0
  let p : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
  have hc : c ≫ limit.π M i = z ≫ p := roosCyclesLimitIso_hom_π M i
  change (h ≫ c) ≫ limit.π M i = h ≫ z ≫ p
  exact (Category.assoc h c (limit.π M i)).trans (congrArg (fun k => h ≫ k) hc)

/-- The class of an cycle has its given coefficient family in the limit. -/
@[reassoc]
theorem roosHomologyπ_zeroIso_hom_π (i : I) :
    (roosComplex M).homologyπ 0 ≫ (roosHomologyZeroIso M).hom ≫ limit.π M i =
      (roosComplex M).iCycles 0 ≫ roosπ M (ComposableArrows.mk₀ (op i)) := by
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let q : (roosComplex M).cycles 0 ⟶ (roosComplex M).homology 0 :=
    (roosComplex M).homologyπ 0
  let h : (roosComplex M).homology 0 ⟶ (roosComplex M).cycles 0 :=
    (roosComplex M).isoHomologyπ₀.inv
  let H : (roosComplex M).homology 0 ⟶ limit M := (roosHomologyZeroIso M).hom
  let z : (roosComplex M).cycles 0 ⟶ X₀ := (roosComplex M).iCycles 0
  let p : X₀ ⟶ M.obj i := roosπ M (ComposableArrows.mk₀ (op i))
  have hH : H ≫ limit.π M i = h ≫ (z ≫ p) := roosHomologyZeroIso_hom_π M i
  have hqh : q ≫ h = 𝟙 ((roosComplex M).cycles 0) := by
    change (roosComplex M).isoHomologyπ₀.hom ≫
      (roosComplex M).isoHomologyπ₀.inv = 𝟙 _
    exact (roosComplex M).isoHomologyπ₀.hom_inv_id
  change q ≫ H ≫ limit.π M i = z ≫ p
  calc
    q ≫ H ≫ limit.π M i = q ≫ (h ≫ (z ≫ p)) := congrArg (fun k => q ≫ k) hH
    _ = (q ≫ h) ≫ (z ≫ p) := (Category.assoc q h (z ≫ p)).symm
    _ = 𝟙 ((roosComplex M).cycles 0) ≫ (z ≫ p) :=
      congrArg (fun k => k ≫ (z ≫ p)) hqh
    _ = z ≫ p := Category.id_comp _

end Homology

/-- The cycles comparison commutes with the map of the two Roos complexes. -/
theorem roosCyclesLimitIso_naturality {M N : I ⥤ A}
    [HasLimit M] [HasLimit N]
    [(roosComplex M).HasHomology 0] [(roosComplex N).HasHomology 0]
    (α : M ⟶ N) :
    HomologicalComplex.cyclesMap (K := roosComplex M) (L := roosComplex N)
        ((roosComplexFunctor (I := I) (A := A)).map α) 0 ≫
          (roosCyclesLimitIso N).hom =
      (roosCyclesLimitIso M).hom ≫ limMap α := by
  let f : roosComplex M ⟶ roosComplex N :=
    (roosComplexFunctor (I := I) (A := A)).map α
  let X_M : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let X_N : A := (roosCosimplicial N).obj (SimplexCategory.mk 0)
  let r : X_M ⟶ X_N := f.f 0
  let g : (roosComplex M).cycles 0 ⟶ (roosComplex N).cycles 0 :=
    HomologicalComplex.cyclesMap (K := roosComplex M) (L := roosComplex N) f 0
  let c_M : (roosComplex M).cycles 0 ⟶ limit M := (roosCyclesLimitIso M).hom
  let c_N : (roosComplex N).cycles 0 ⟶ limit N := (roosCyclesLimitIso N).hom
  let l_M : limit M ⟶ X_M := roosLimitToZero M
  let l_N : limit N ⟶ X_N := roosLimitToZero N
  let z_M : (roosComplex M).cycles 0 ⟶ X_M := (roosComplex M).iCycles 0
  let z_N : (roosComplex N).cycles 0 ⟶ X_N := (roosComplex N).iCycles 0
  have hM : c_M ≫ l_M = z_M := roosCyclesLimitIso_hom_lift M
  have hN : c_N ≫ l_N = z_N := roosCyclesLimitIso_hom_lift N
  have hg : g ≫ z_N = z_M ≫ r :=
    HomologicalComplex.cyclesMap_i (K := roosComplex M) (L := roosComplex N) f 0
  have hl : limMap α ≫ l_N = l_M ≫ r := roosLimitToZero_naturality α
  have : Mono l_N := Fork.IsLimit.mono (roosKernelForkIsLimit N)
  change g ≫ c_N = c_M ≫ limMap α
  apply (cancel_mono l_N).1
  calc
    (g ≫ c_N) ≫ l_N = g ≫ (c_N ≫ l_N) := Category.assoc _ _ _
    _ = g ≫ z_N := congrArg (fun k => g ≫ k) hN
    _ = z_M ≫ r := hg
    _ = (c_M ≫ l_M) ≫ r := congrArg (fun k => k ≫ r) hM.symm
    _ = c_M ≫ (l_M ≫ r) := Category.assoc _ _ _
    _ = c_M ≫ (limMap α ≫ l_N) := congrArg (fun k => c_M ≫ k) hl.symm
    _ = (c_M ≫ limMap α) ≫ l_N := (Category.assoc _ _ _).symm

/-- The comparison uses the homology map of the Roos cochain map. -/
theorem roosHomologyZeroIso_naturality {M N : I ⥤ A}
    [HasLimit M] [HasLimit N]
    [(roosComplex M).HasHomology 0] [(roosComplex N).HasHomology 0]
    (α : M ⟶ N) :
    HomologicalComplex.homologyMap (K := roosComplex M) (L := roosComplex N)
        ((roosComplexFunctor (I := I) (A := A)).map α) 0 ≫
          (roosHomologyZeroIso N).hom =
      (roosHomologyZeroIso M).hom ≫ limMap α := by
  let f : roosComplex M ⟶ roosComplex N :=
    (roosComplexFunctor (I := I) (A := A)).map α
  let g : (roosComplex M).homology 0 ⟶ (roosComplex N).homology 0 :=
    HomologicalComplex.homologyMap (K := roosComplex M) (L := roosComplex N) f 0
  let t : (roosComplex M).cycles 0 ⟶ (roosComplex N).cycles 0 :=
    HomologicalComplex.cyclesMap (K := roosComplex M) (L := roosComplex N) f 0
  let h_M : (roosComplex M).homology 0 ⟶ (roosComplex M).cycles 0 :=
    (roosComplex M).isoHomologyπ₀.inv
  let h_N : (roosComplex N).homology 0 ⟶ (roosComplex N).cycles 0 :=
    (roosComplex N).isoHomologyπ₀.inv
  let c_M : (roosComplex M).cycles 0 ⟶ limit M := (roosCyclesLimitIso M).hom
  let c_N : (roosComplex N).cycles 0 ⟶ limit N := (roosCyclesLimitIso N).hom
  have hπ : g ≫ h_N = h_M ≫ t :=
    CochainComplex.isoHomologyπ₀_inv_naturality (K := roosComplex M) (L := roosComplex N) f
  have hc : t ≫ c_N = c_M ≫ limMap α := roosCyclesLimitIso_naturality α
  change g ≫ (h_N ≫ c_N) = (h_M ≫ c_M) ≫ limMap α
  calc
    g ≫ (h_N ≫ c_N) = (g ≫ h_N) ≫ c_N := (Category.assoc _ _ _).symm
    _ = (h_M ≫ t) ≫ c_N := congrArg (fun k => k ≫ c_N) hπ
    _ = h_M ≫ (t ≫ c_N) := Category.assoc _ _ _
    _ = h_M ≫ (c_M ≫ limMap α) := congrArg (fun k => h_M ≫ k) hc
    _ = (h_M ≫ c_M) ≫ limMap α := (Category.assoc _ _ _).symm

section HomologyFunctor

variable [HasLimitsOfShape I A] [CategoryWithHomology A]

/-- The homology functor of the Roos complex is naturally `lim`. -/
def roosHomologyZeroNatIso :
    (roosComplexFunctor (I := I) (A := A) ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0) ≅ lim :=
  NatIso.ofComponents (fun M ↦ roosHomologyZeroIso M)
    (fun {_ _} α ↦ roosHomologyZeroIso_naturality α)

/-- The component of the natural degree-zero limit comparison is the degree-zero Roos homology
isomorphism for that diagram. -/
@[simp]
theorem roosHomologyZeroNatIso_hom_app (M : I ⥤ A) :
    (roosHomologyZeroNatIso (I := I) (A := A)).hom.app M =
      (roosHomologyZeroIso M).hom := rfl

end HomologyFunctor

end CategoryTheory.CategoryCohomology

end
