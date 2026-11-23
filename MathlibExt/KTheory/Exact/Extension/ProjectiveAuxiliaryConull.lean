/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.KTheory.Exact.Extension.AuxiliaryUnitRow
public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWHWeakHSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction
public import MathlibExt.Topology.Homotopy.CGWHWeakHSpacePositiveGroups
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyGroupIso
public import MathlibExt.Topology.Category.TopCat.WeakHomotopySingleton
public import MathlibExt.AlgebraicTopology.SimplicialSet.ConullWeakHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveRealizedIsoPath
public import MathlibExt.KTheory.Exact.Extension.SplitRowInclusion

/-!
# The projective auxiliary conull weak equivalence

The auxiliary category consists of fixed-quotient extension rows with
stabilized morphisms. Its pullback convolution and diagonal give a native
weak-unit multiplication with the chosen root path and its reversed trace.

For every associative unital ring and finitely generated projective quotient
module, the unit-to-row construction gives connectedness. The positive
homotopy groups of the native realization are trivial and transport to the
ordinary realization. The final theorem concerns the literal terminal map
of the original auxiliary nerve.

The generic trace, native cube, singleton-target and inverse-edge results
come from the focused topology and simplicial-set modules. The split row is
`SplitInclusion.splitRow` at the actual Core object `⟨A⟩`; its original row
projections and stabilizer data are retained.

The pullback auxiliary category and diagonal follow Weibel Proposition
IV.7.6, printed pp.329–330 / PDF pp.337–338. Exercise IV.7.6 contains the
cofibered construction with pushouts.

Object, Hom, compact-probe and carrier universes remain independent.
-/

universe w u v k

open CategoryTheory.Preadditive


@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

/-- The original auxiliary category L, with no denominator coordinate. -/
abbrev Auxiliary (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) :=
  MonoidalActionCategory (Core C) (FixedTargetExtension C X)

/-- The corresponding actual auxiliary object, without replacing X by a zero fiber. -/
def auxiliaryUnit (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) : Auxiliary C X :=
  ⟨unitRow X⟩

/-- The exact original row determines an admissible-epi kernel presentation. -/
def rowKernelPresentation (E : FixedTargetExtension C X) :
    AdmissibleEpiKernelPresentation E.p where
  kernel := E.A
  ι := E.i
  zero := E.zero
  exact := by exact E.admissible

/-- The middle object is the actual pullback of the original quotient along itself. -/
def selfPullback (E : FixedTargetExtension C X) :
    (rowKernelPresentation E).BaseChange E.p :=
  (rowKernelPresentation E).baseChange E.p

/-- Extract the original kernel element of the difference of the two middle legs. -/
def selfDifference (E : FixedTargetExtension C X) : (selfPullback E).obj ⟶ E.A := by
  let P := selfPullback E
  have w : (P.snd - P.fst) ≫ E.p = 0 := by
    rw [sub_comp, P.square.w, sub_self]
  exact (rowKernelPresentation E).kernelIsLimit.lift
    (KernelFork.ofι (P.snd - P.fst) w)

/-- The extracted kernel map has precisely the actual middle difference as its image. -/
theorem selfDifference_i (E : FixedTargetExtension C X) :
    selfDifference E ≫ E.i = (selfPullback E).snd - (selfPullback E).fst := by
  exact (rowKernelPresentation E).kernelIsLimit.fac _ WalkingParallelPair.zero

/-- The original middle diagonal into its independently chosen pullback. -/
def middleDiagonal (E : FixedTargetExtension C X) : E.B ⟶ (selfPullback E).obj :=
  (selfPullback E).square.lift (𝟙 E.B) (𝟙 E.B) (by simp)

theorem middleDiagonal_fst (E : FixedTargetExtension C X) :
    middleDiagonal E ≫ (selfPullback E).fst = 𝟙 E.B :=
  (selfPullback E).square.lift_fst _ _ _

theorem middleDiagonal_snd (E : FixedTargetExtension C X) :
    middleDiagonal E ≫ (selfPullback E).snd = 𝟙 E.B :=
  (selfPullback E).square.lift_snd _ _ _

/-- The actual forward middle map is `(a,b) ↦ (b,i(a)+b)`. -/
def middleForward (E : FixedTargetExtension C X) : E.A ⊞ E.B ⟶ (selfPullback E).obj :=
  (selfPullback E).square.lift biprod.snd
    ((biprod.fst : E.A ⊞ E.B ⟶ E.A) ≫ E.i + biprod.snd) (by
      simp only [add_comp, Category.assoc, E.zero, comp_zero, zero_add])

theorem middleForward_fst (E : FixedTargetExtension C X) :
    middleForward E ≫ (selfPullback E).fst = (biprod.snd : E.A ⊞ E.B ⟶ E.B) :=
  (selfPullback E).square.lift_fst _ _ _

theorem middleForward_snd (E : FixedTargetExtension C X) :
    middleForward E ≫ (selfPullback E).snd =
      (biprod.fst : E.A ⊞ E.B ⟶ E.A) ≫ E.i + biprod.snd :=
  (selfPullback E).square.lift_snd _ _ _

/-- Its difference recovers the original first summand, using the genuine kernel mono. -/
theorem middleForward_difference (E : FixedTargetExtension C X) :
    middleForward E ≫ selfDifference E = (biprod.fst : E.A ⊞ E.B ⟶ E.A) := by
  have hMono : Mono E.i := (isAdmissibleMono_f E.admissible).mono
  apply hMono.right_cancellation
  rw [Category.assoc, selfDifference_i, comp_sub,
    middleForward_snd, middleForward_fst, add_sub_cancel_right]

/-- The inverse middle map is `(b1,b2) ↦ (kernel(b2-b1),b1)`. -/
def middleInverse (E : FixedTargetExtension C X) : (selfPullback E).obj ⟶ E.A ⊞ E.B :=
  biprod.lift (selfDifference E) (selfPullback E).fst

/-- The middle isomorphism is derived from the exact kernel and the actual pullback. -/
def selfMiddleIso (E : FixedTargetExtension C X) : E.A ⊞ E.B ≅ (selfPullback E).obj where
  hom := middleForward E
  inv := middleInverse E
  hom_inv_id := by
    apply biprod.hom_ext
    · simp only [middleInverse, Category.assoc, biprod.lift_fst,
        middleForward_difference, Category.id_comp]
    · simp only [middleInverse, Category.assoc, biprod.lift_snd,
        middleForward_fst, Category.id_comp]
  inv_hom_id := by
    apply (selfPullback E).square.hom_ext
    · simp only [Category.assoc, middleForward_fst, middleInverse,
        biprod.lift_snd, Category.id_comp]
    · simp only [Category.assoc, middleForward_snd, middleInverse, comp_add,
        biprod.lift_fst_assoc, biprod.lift_snd, selfDifference_i,
        sub_add_cancel, Category.id_comp]

/-- The corresponding kernel map is `(a1,a2) ↦ (a2,a1+a2)`. -/
def selfKernelIso (E : FixedTargetExtension C X) : E.A ⊞ E.A ≅ E.A ⊞ E.A where
  hom := biprod.lift biprod.snd (biprod.fst + biprod.snd)
  inv := biprod.lift (biprod.snd - biprod.fst) biprod.fst
  hom_inv_id := by
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, comp_sub,
        add_sub_cancel_right, Category.id_comp]
  inv_hom_id := by
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, comp_add,
        sub_add_cancel, Category.id_comp]

/-- The actual self-convolution kernel has one original inclusion on each middle leg. -/
def selfKernelInclusion (E : FixedTargetExtension C X) :
    E.A ⊞ E.A ⟶ (selfPullback E).obj :=
  (selfPullback E).square.lift
    ((biprod.fst : E.A ⊞ E.A ⟶ E.A) ≫ E.i)
    ((biprod.snd : E.A ⊞ E.A ⟶ E.A) ≫ E.i) (by
      simp only [Category.assoc, E.zero, comp_zero])

theorem selfKernelInclusion_fst (E : FixedTargetExtension C X) :
    selfKernelInclusion E ≫ (selfPullback E).fst =
      (biprod.fst : E.A ⊞ E.A ⟶ E.A) ≫ E.i :=
  (selfPullback E).square.lift_fst _ _ _

theorem selfKernelInclusion_snd (E : FixedTargetExtension C X) :
    selfKernelInclusion E ≫ (selfPullback E).snd =
      (biprod.snd : E.A ⊞ E.A ⟶ E.A) ≫ E.i :=
  (selfPullback E).square.lift_snd _ _ _

/-- The kernel matrix and forward middle map form the actual row square. -/
theorem kernel_middle_square (E : FixedTargetExtension C X) :
    (selfKernelIso E).hom ≫ selfKernelInclusion E =
      biprod.map (𝟙 E.A) E.i ≫ middleForward E := by
  apply (selfPullback E).square.hom_ext
  · simp only [Category.assoc, selfKernelInclusion_fst, selfKernelIso,
      biprod.lift_fst_assoc, middleForward_fst, biprod.map_snd]
  · simp only [Category.assoc, selfKernelInclusion_snd, selfKernelIso,
      biprod.lift_snd_assoc, middleForward_snd, comp_add,
      biprod.map_fst_assoc, biprod.map_snd, add_comp, Category.id_comp]

/-- The original given quotient remains unchanged in the derived middle square. -/
theorem middle_quotient_square (E : FixedTargetExtension C X) :
    middleForward E ≫ ((selfPullback E).fst ≫ E.p) =
      ((biprod.snd : E.A ⊞ E.B ⟶ E.B) ≫ E.p) ≫ 𝟙 X := by
  rw [← Category.assoc, middleForward_fst, Category.comp_id]

/-- The actual pullback kernel and quotient compose to zero. -/
theorem selfKernelInclusion_zero (E : FixedTargetExtension C X) :
    selfKernelInclusion E ≫ ((selfPullback E).fst ≫ E.p) = 0 := by
  rw [← Category.assoc, selfKernelInclusion_fst, Category.assoc, E.zero, comp_zero]

/-- The independently chosen original pullback row is genuinely admissible. -/
theorem selfConvolution_admissible (E : FixedTargetExtension C X) :
    IsAdmissibleExact (ShortComplex.mk (selfKernelInclusion E)
      ((selfPullback E).fst ≫ E.p) (selfKernelInclusion_zero E)) := by
  let S := (FixedTargetExtension.leftSumObj (⟨E.A⟩ : Core C) E).toExtension.row
  let T := ShortComplex.mk (selfKernelInclusion E)
    ((selfPullback E).fst ≫ E.p) (selfKernelInclusion_zero E)
  let e : S ≅ T := ShortComplex.isoMk (selfKernelIso E) (selfMiddleIso E)
    (Iso.refl X) (by exact kernel_middle_square E) (by exact middle_quotient_square E)
  exact isAdmissibleExact_of_iso e
    (FixedTargetExtension.leftSumObj (⟨E.A⟩ : Core C) E).admissible

/-- The actual doubled row has kernel A⊞A and middle B×_X B. -/
def selfConvolution (E : FixedTargetExtension C X) : FixedTargetExtension C X where
  A := E.A ⊞ E.A
  B := (selfPullback E).obj
  i := selfKernelInclusion E
  p := (selfPullback E).fst ≫ E.p
  zero := by exact selfKernelInclusion_zero E
  admissible := by exact selfConvolution_admissible E

/-- The original A-stabilized row maps isomorphically to the actual doubled row. -/
def diagonalRowIso (E : FixedTargetExtension C X) :
    FixedTargetExtension.leftSumObj (⟨E.A⟩ : Core C) E ≅ selfConvolution E := by
  let h : FixedTargetExtension.leftSumObj (⟨E.A⟩ : Core C) E ⟶ selfConvolution E :=
    { a := selfKernelIso E
      b := selfMiddleIso E
      comm_i := by exact (kernel_middle_square E).symm
      comm_p := by
        exact (middle_quotient_square E).trans (Category.comp_id _) }
  exact FixedTargetExtension.pairIso h

/-- The actual raw auxiliary diagonal keeps the original kernel A as its stabilizer. -/
def diagonalRaw (E : FixedTargetExtension C X) :
    RawHom (⟨E⟩ : Auxiliary C X) ⟨selfConvolution E⟩ where
  stabilizer := ⟨E.A⟩
  hom := (diagonalRowIso E).hom

/-- Its quotient class is the original auxiliary arrow E→E*E. -/
def diagonalArrow (E : FixedTargetExtension C X) :
    (⟨E⟩ : Auxiliary C X) ⟶ ⟨selfConvolution E⟩ :=
  MonoidalActionCategory.Hom.mk (diagonalRaw E)

theorem diagonalRaw_stabilizer (E : FixedTargetExtension C X) :
    (diagonalRaw E).stabilizer = (⟨E.A⟩ : Core C) := rfl

/-- Restriction to the original B is the literal diagonal, not a chosen section map. -/
theorem diagonalRaw_middle_inr (E : FixedTargetExtension C X) :
    (biprod.inr : E.B ⟶ E.A ⊞ E.B) ≫ (diagonalRaw E).hom.b.hom =
      middleDiagonal E := by
  change (biprod.inr : E.B ⟶ E.A ⊞ E.B) ≫ middleForward E = middleDiagonal E
  apply (selfPullback E).square.hom_ext
  · rw [Category.assoc, middleForward_fst, biprod.inr_snd, middleDiagonal_fst]
  · rw [Category.assoc, middleForward_snd, comp_add,
      biprod.inr_fst_assoc, zero_comp, zero_add, biprod.inr_snd, middleDiagonal_snd]

/-- The nerve is that of the same auxiliary category, in common max(u,v). -/
def auxiliaryNerve (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) :
    SSet.{max u v} := nerve (Auxiliary C X)

/-- The independently defined original auxiliary realization. -/
def auxiliarySpace (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) :
    TopCat.{max u v} := SSet.toTop.obj (auxiliaryNerve C X)

/-- The actual auxiliary object vertex, with the original row retained. -/
def auxiliaryVertex (E : FixedTargetExtension C X) : auxiliarySpace C X :=
  SSet.realizedVertex (nerveEquiv.symm (⟨E⟩ : Auxiliary C X))

/-- The selected unit point is the realized vertex of the literal unit row. -/
def auxiliaryUnitPoint (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) : auxiliarySpace C X :=
  SSet.realizedVertex (nerveEquiv.symm (auxiliaryUnit C X))

/-- The actual one-simplex of the auxiliary diagonal arrow. -/
def diagonalEdge (E : FixedTargetExtension C X) :
    (auxiliaryNerve C X).Edge (nerveEquiv.symm (⟨E⟩ : Auxiliary C X))
      (nerveEquiv.symm (⟨selfConvolution E⟩ : Auxiliary C X)) :=
  CategoryTheory.nerve.edgeMk (diagonalArrow E)

/-- Its realized path runs from E to the original doubled pullback row. -/
def diagonalPath (E : FixedTargetExtension C X) :
    (auxiliarySpace C X).Path (auxiliaryVertex E) (auxiliaryVertex (selfConvolution E)) :=
  SSet.realizedEdgePath (diagonalEdge E)

end AlgebraicKTheory.AuxiliaryExtension

end

/-!
# Binary convolution of the same original given-X rows

The middle pullback is chosen from the admissible-epi axiom. The explicit
biproduct of the two original kernels is proved to be its composite kernel;
admissibility is then transported from the actual admissible-epi presentation.
No availability of unrelated pullbacks and no splitting is assumed.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

/-- The actual middle pullback has first leg E.B and second leg F.B. -/
def convolutionPullback (E F : FixedTargetExtension C X) :
    (rowKernelPresentation F).BaseChange E.p :=
  (rowKernelPresentation F).baseChange E.p

/-- The original common quotient is obtained by the first actual projection. -/
def convolutionQuotient (E F : FixedTargetExtension C X) :
    (convolutionPullback E F).obj ⟶ X :=
  (convolutionPullback E F).fst ≫ E.p

/-- The explicit kernel inclusion has the two original inclusions as its legs. -/
def convolutionKernel (E F : FixedTargetExtension C X) :
    E.A ⊞ F.A ⟶ (convolutionPullback E F).obj :=
  (convolutionPullback E F).square.lift
    ((biprod.fst : E.A ⊞ F.A ⟶ E.A) ≫ E.i)
    ((biprod.snd : E.A ⊞ F.A ⟶ F.A) ≫ F.i) (by
      simp only [Category.assoc, E.zero, F.zero, comp_zero])

@[reassoc (attr := simp)]
theorem convolutionKernel_fst (E F : FixedTargetExtension C X) :
    convolutionKernel E F ≫ (convolutionPullback E F).fst =
      (biprod.fst : E.A ⊞ F.A ⟶ E.A) ≫ E.i :=
  (convolutionPullback E F).square.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem convolutionKernel_snd (E F : FixedTargetExtension C X) :
    convolutionKernel E F ≫ (convolutionPullback E F).snd =
      (biprod.snd : E.A ⊞ F.A ⟶ F.A) ≫ F.i :=
  (convolutionPullback E F).square.lift_snd _ _ _

theorem convolutionKernel_zero (E F : FixedTargetExtension C X) :
    convolutionKernel E F ≫ convolutionQuotient E F = 0 := by
  change convolutionKernel E F ≫ ((convolutionPullback E F).fst ≫ E.p) = 0
  rw [← Category.assoc, convolutionKernel_fst, Category.assoc, E.zero, comp_zero]

/-- The actual common quotient is admissible epi, by composition of actual epis. -/
theorem convolutionQuotient_admissible (E F : FixedTargetExtension C X) :
    IsAdmissibleEpi (convolutionQuotient E F) :=
  admissibleEpi_comp.comp_mem _ _ (convolutionPullback E F).fst_admissible
    (isAdmissibleEpi_g E.admissible)

/-- Pin the original kernel fork before it is used by a dependent lift. -/
def originalRowKernelLimit (E : FixedTargetExtension C X) :
    IsLimit (KernelFork.ofι E.i E.zero) :=
  (rowKernelPresentation E).kernelIsLimit

private theorem convolutionKernelLift_fst_zero (E F : FixedTargetExtension C X) {W : C}
    (h : W ⟶ (convolutionPullback E F).obj)
    (hh : h ≫ convolutionQuotient E F = 0) :
    (h ≫ (convolutionPullback E F).fst) ≫ E.p = 0 := by
  let P := convolutionPullback E F
  have hq : convolutionQuotient E F = P.fst ≫ E.p := rfl
  have hhP : h ≫ (P.fst ≫ E.p) = 0 :=
    (congrArg (fun q : P.obj ⟶ X => h ≫ q) hq).symm.trans hh
  exact (Category.assoc h P.fst E.p).trans hhP

private theorem convolutionKernelLift_snd_zero (E F : FixedTargetExtension C X) {W : C}
    (h : W ⟶ (convolutionPullback E F).obj)
    (hh : h ≫ convolutionQuotient E F = 0) :
    (h ≫ (convolutionPullback E F).snd) ≫ F.p = 0 := by
  let P := convolutionPullback E F
  have hq : convolutionQuotient E F = P.fst ≫ E.p := rfl
  have hhP : h ≫ (P.fst ≫ E.p) = 0 :=
    (congrArg (fun q : P.obj ⟶ X => h ≫ q) hq).symm.trans hh
  exact (Category.assoc h P.snd F.p).trans
    ((congrArg (fun q : P.obj ⟶ X => h ≫ q) P.square.w.symm).trans hhP)

/-- The actual pair of the two original kernel lifts, with opaque typed proof boundaries. -/
def convolutionKernelLift (E F : FixedTargetExtension C X) {W : C}
    (h : W ⟶ (convolutionPullback E F).obj)
    (hh : h ≫ convolutionQuotient E F = 0) : W ⟶ E.A ⊞ F.A :=
  biprod.lift
    ((originalRowKernelLimit E).lift
      (KernelFork.ofι (h ≫ (convolutionPullback E F).fst)
        (by exact convolutionKernelLift_fst_zero E F h hh)))
    ((originalRowKernelLimit F).lift
      (KernelFork.ofι (h ≫ (convolutionPullback E F).snd)
        (by exact convolutionKernelLift_snd_zero E F h hh)))

private theorem convolutionKernelLift_fst_i (E F : FixedTargetExtension C X) {W : C}
    (h : W ⟶ (convolutionPullback E F).obj)
    (hh : h ≫ convolutionQuotient E F = 0) :
    (convolutionKernelLift E F h hh ≫ biprod.fst) ≫ E.i =
      h ≫ (convolutionPullback E F).fst := by
  unfold convolutionKernelLift
  rw [biprod.lift_fst]
  exact (originalRowKernelLimit E).fac _ WalkingParallelPair.zero

private theorem convolutionKernelLift_snd_i (E F : FixedTargetExtension C X) {W : C}
    (h : W ⟶ (convolutionPullback E F).obj)
    (hh : h ≫ convolutionQuotient E F = 0) :
    (convolutionKernelLift E F h hh ≫ biprod.snd) ≫ F.i =
      h ≫ (convolutionPullback E F).snd := by
  unfold convolutionKernelLift
  rw [biprod.lift_snd]
  exact (originalRowKernelLimit F).fac _ WalkingParallelPair.zero

/-- The two original kernel universal properties give the composite kernel. -/
def convolutionKernelIsLimit (E F : FixedTargetExtension C X) :
    IsLimit (KernelFork.ofι (convolutionKernel E F) (convolutionKernel_zero E F)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} h hh => convolutionKernelLift E F h hh)
    (fun {W} h hh => by
      apply (convolutionPullback E F).square.hom_ext
      · rw [Category.assoc, convolutionKernel_fst, ← Category.assoc]
        exact convolutionKernelLift_fst_i E F h hh
      · rw [Category.assoc, convolutionKernel_snd, ← Category.assoc]
        exact convolutionKernelLift_snd_i E F h hh)
    (fun {W} h hh m hm => by
      have hMonoE : Mono E.i := (isAdmissibleMono_f E.admissible).mono
      have hMonoF : Mono F.i := (isAdmissibleMono_f F.admissible).mono
      apply biprod.hom_ext
      · apply hMonoE.right_cancellation
        have he := congrArg
          (fun q : W ⟶ (convolutionPullback E F).obj =>
            q ≫ (convolutionPullback E F).fst) hm
        rw [Category.assoc, convolutionKernel_fst, ← Category.assoc] at he
        exact he.trans (convolutionKernelLift_fst_i E F h hh).symm
      · apply hMonoF.right_cancellation
        have he := congrArg
          (fun q : W ⟶ (convolutionPullback E F).obj =>
            q ≫ (convolutionPullback E F).snd) hm
        rw [Category.assoc, convolutionKernel_snd, ← Category.assoc] at he
        exact he.trans (convolutionKernelLift_snd_i E F h hh).symm)

/-- The original biproduct-kernel pullback row is genuinely admissible. -/
theorem convolution_admissible (E F : FixedTargetExtension C X) :
    IsAdmissibleExact (ShortComplex.mk (convolutionKernel E F)
      (convolutionQuotient E F) (convolutionKernel_zero E F)) := by
  let J := (AdmissibleEpiKernelPresentation.nonempty
    (convolutionQuotient_admissible E F)).some
  let hK := convolutionKernelIsLimit E F
  let hJ := J.kernelIsLimit
  let e : E.A ⊞ F.A ≅ J.kernel := hK.conePointUniqueUpToIso hJ
  have he : e.hom ≫ J.ι = convolutionKernel E F := by
    have h := IsLimit.conePointUniqueUpToIso_hom_comp hK hJ WalkingParallelPair.zero
    simpa [KernelFork.ofι] using h
  let S := ShortComplex.mk (convolutionKernel E F)
    (convolutionQuotient E F) (convolutionKernel_zero E F)
  let T := ShortComplex.mk J.ι (convolutionQuotient E F) J.zero
  let eRow : S ≅ T := ShortComplex.isoMk e (Iso.refl _) (Iso.refl X)
    (by simpa [S, T] using he) (by simp [S, T])
  exact isAdmissibleExact_of_iso eRow.symm J.exact

/-- Weibel's literal convolution row A_E⊞A_F→B_E×_X B_F→X. -/
def convolutionObj (E F : FixedTargetExtension C X) : FixedTargetExtension C X where
  A := E.A ⊞ F.A
  B := (convolutionPullback E F).obj
  i := convolutionKernel E F
  p := convolutionQuotient E F
  zero := by exact convolutionKernel_zero E F
  admissible := by exact convolution_admissible E F

/-- The actual row middle is the chosen original pullback object. -/
theorem convolutionObj_middle_eq (E F : FixedTargetExtension C X) :
    (convolutionObj E F).B = (convolutionPullback E F).obj := rfl

/-- The canonical object transport retains the actual row and pullback endpoints. -/
def convolutionObjMiddleIso (E F : FixedTargetExtension C X) :
    (convolutionObj E F).B ≅ (convolutionPullback E F).obj :=
  eqToIso (convolutionObj_middle_eq E F)

private theorem convolutionObj_kernel_eq (E F : FixedTargetExtension C X) :
    ((convolutionObj E F).A) = (E.A ⊞ F.A) := rfl

private theorem leftSumObj_kernel_eq (T : Core C) (E : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj T E).A) = (T.of ⊞ E.A) := rfl

private theorem leftSumObj_middle_eq (T : Core C) (E : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj T E).B) = (T.of ⊞ E.B) := rfl

private theorem convolutionObj_i_heq (E F : FixedTargetExtension C X) :
    HEq (convolutionObj E F).i (convolutionKernel E F) := by rfl

private theorem convolutionObj_p_heq (E F : FixedTargetExtension C X) :
    HEq (convolutionObj E F).p (convolutionQuotient E F) := by rfl

private theorem convolutionObj_i_conjugate (E F : FixedTargetExtension C X) :
    (convolutionObj E F).i =
      (eqToIso (convolutionObj_kernel_eq E F)).hom ≫ convolutionKernel E F ≫
        (convolutionObjMiddleIso E F).inv := by
  have h := (conj_eqToHom_iff_heq (convolutionObj E F).i (convolutionKernel E F)
    (convolutionObj_kernel_eq E F) (convolutionObj_middle_eq E F)).2
      (convolutionObj_i_heq E F)
  simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToIso.inv] using h

private theorem convolutionObj_kernel_transport (E F : FixedTargetExtension C X) :
    (eqToIso (convolutionObj_kernel_eq E F)).inv ≫ (convolutionObj E F).i ≫
      (convolutionObjMiddleIso E F).hom = convolutionKernel E F := by
  rw [convolutionObj_i_conjugate]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem convolutionObj_middleIso_hom_p (E F : FixedTargetExtension C X) :
    (convolutionObjMiddleIso E F).hom ≫ convolutionQuotient E F =
      (convolutionObj E F).p := by
  have h := (conj_eqToHom_iff_heq (convolutionObj E F).p (convolutionQuotient E F)
    (convolutionObj_middle_eq E F) (rfl : X = X)).2 (convolutionObj_p_heq E F)
  simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToHom_refl,
    Category.comp_id] using h.symm

private theorem convolutionObj_middleIso_inv_p (E F : FixedTargetExtension C X) :
    (convolutionObjMiddleIso E F).inv ≫ (convolutionObj E F).p =
      convolutionQuotient E F := by
  rw [← convolutionObj_middleIso_hom_p]
  simp only [Iso.inv_hom_id_assoc]

private theorem convolutionObj_i_post_middle (E F : FixedTargetExtension C X) :
    (convolutionObj E F).i ≫ (convolutionObjMiddleIso E F).hom =
      (eqToIso (convolutionObj_kernel_eq E F)).hom ≫ convolutionKernel E F := by
  rw [convolutionObj_i_conjugate]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem leftSumObj_i_heq (T : Core C) (E : FixedTargetExtension C X) :
    HEq (FixedTargetExtension.leftSumObj T E).i (biprod.map (𝟙 T.of) E.i) := by rfl

private theorem leftSumObj_p_heq (T : Core C) (E : FixedTargetExtension C X) :
    HEq (FixedTargetExtension.leftSumObj T E).p
      ((biprod.snd : T.of ⊞ E.B ⟶ E.B) ≫ E.p) := by rfl

private theorem leftSumObj_i_conjugate (T : Core C) (E : FixedTargetExtension C X) :
    (FixedTargetExtension.leftSumObj T E).i =
      (eqToIso (leftSumObj_kernel_eq T E)).hom ≫ biprod.map (𝟙 T.of) E.i ≫
        (eqToIso (leftSumObj_middle_eq T E)).inv := by
  have h := (conj_eqToHom_iff_heq (FixedTargetExtension.leftSumObj T E).i
    (biprod.map (𝟙 T.of) E.i) (leftSumObj_kernel_eq T E)
    (leftSumObj_middle_eq T E)).2 (leftSumObj_i_heq T E)
  simpa only [eqToIso.hom, eqToIso.inv] using h

private theorem leftSumObj_i_pre_kernel (T : Core C) (E : FixedTargetExtension C X) :
    (eqToIso (leftSumObj_kernel_eq T E)).inv ≫ (FixedTargetExtension.leftSumObj T E).i =
      biprod.map (𝟙 T.of) E.i ≫ (eqToIso (leftSumObj_middle_eq T E)).inv := by
  rw [leftSumObj_i_conjugate]
  simp only [Iso.inv_hom_id_assoc]

private theorem leftSumObj_middleIso_hom_p (T : Core C) (E : FixedTargetExtension C X) :
    (eqToIso (leftSumObj_middle_eq T E)).hom ≫
      (biprod.snd : T.of ⊞ E.B ⟶ E.B) ≫ E.p =
        (FixedTargetExtension.leftSumObj T E).p := by
  have h := (conj_eqToHom_iff_heq (FixedTargetExtension.leftSumObj T E).p
    ((biprod.snd : T.of ⊞ E.B ⟶ E.B) ≫ E.p)
    (leftSumObj_middle_eq T E) (rfl : X = X)).2 (leftSumObj_p_heq T E)
  simpa only [eqToIso.hom, eqToHom_refl, Category.comp_id] using h.symm

private theorem leftSumObj_middleIso_inv_p (T : Core C) (E : FixedTargetExtension C X) :
    (eqToIso (leftSumObj_middle_eq T E)).inv ≫
      (FixedTargetExtension.leftSumObj T E).p =
        (biprod.snd : T.of ⊞ E.B ⟶ E.B) ≫ E.p := by
  rw [← leftSumObj_middleIso_hom_p]
  simp only [Iso.inv_hom_id_assoc]

open scoped CategoryTheory.MonoidalCategory CategoryTheory.Limits.CoreBiprodMonoidal

private theorem leftSumTensor_middle_eq (T U : Core C) (E F : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).B) =
      ((T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj) := by rfl

/-- The map of actual pullback middles follows the two original middle isomorphisms. -/
def convolutionMiddleMap {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    (convolutionPullback E F).obj ⟶ (convolutionPullback E' F').obj :=
  (convolutionPullback E' F').square.lift
    ((convolutionPullback E F).fst ≫ f.b.hom)
    ((convolutionPullback E F).snd ≫ g.b.hom) (by
      simpa only [Category.assoc, f.comm_p, g.comm_p] using
        (convolutionPullback E F).square.w)

@[reassoc (attr := simp)]
theorem convolutionMiddleMap_fst {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    convolutionMiddleMap f g ≫ (convolutionPullback E' F').fst =
      (convolutionPullback E F).fst ≫ f.b.hom :=
  (convolutionPullback E' F').square.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem convolutionMiddleMap_snd {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    convolutionMiddleMap f g ≫ (convolutionPullback E' F').snd =
      (convolutionPullback E F).snd ≫ g.b.hom :=
  (convolutionPullback E' F').square.lift_snd _ _ _

/-- The inverse pullback map uses the actual inverses of the two original row maps. -/
def convolutionMiddleIso {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    (convolutionPullback E F).obj ≅ (convolutionPullback E' F').obj where
  hom := convolutionMiddleMap f g
  inv := convolutionMiddleMap (FixedTargetExtension.Hom.symm f)
    (FixedTargetExtension.Hom.symm g)
  hom_inv_id := by
    apply (convolutionPullback E F).square.hom_ext
    · simp only [Category.assoc, convolutionMiddleMap_fst,
        convolutionMiddleMap_fst_assoc, FixedTargetExtension.Hom.symm,
        Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, convolutionMiddleMap_snd,
        convolutionMiddleMap_snd_assoc, FixedTargetExtension.Hom.symm,
        Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (convolutionPullback E' F').square.hom_ext
    · simp only [Category.assoc, convolutionMiddleMap_fst,
        convolutionMiddleMap_fst_assoc, FixedTargetExtension.Hom.symm,
        Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, convolutionMiddleMap_snd,
        convolutionMiddleMap_snd_assoc, FixedTargetExtension.Hom.symm,
        Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The actual given-X row map pairs the biproduct kernel Iso and pullback middle Iso. -/
def convolutionMap {E E' F F' : FixedTargetExtension C X} (f : E ⟶ E') (g : F ⟶ F') :
    convolutionObj E F ⟶ convolutionObj E' F' where
  a := biprod.mapIso f.a g.a
  b := convolutionMiddleIso f g
  comm_i := by
    change convolutionKernel E F ≫ convolutionMiddleMap f g =
      biprod.map f.a.hom g.a.hom ≫ convolutionKernel E' F'
    apply (convolutionPullback E' F').square.hom_ext
    · simp only [Category.assoc, convolutionMiddleMap_fst,
        convolutionKernel_fst, convolutionKernel_fst_assoc, biprod.map_fst_assoc, f.comm_i]
    · simp only [Category.assoc, convolutionMiddleMap_snd,
        convolutionKernel_snd, convolutionKernel_snd_assoc, biprod.map_snd_assoc, g.comm_i]
  comm_p := by
    change convolutionMiddleMap f g ≫ convolutionQuotient E' F' = convolutionQuotient E F
    simp only [convolutionQuotient, convolutionMiddleMap_fst_assoc, f.comm_p]

/-- Its forward middle map is exactly the map of the two original pullback legs. -/
theorem convolutionMap_middle {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    (convolutionMap f g).b.hom = convolutionMiddleMap f g := rfl

/-- The original kernel map is exactly the biproduct of the two original kernel maps. -/
theorem convolutionMap_kernel {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    (convolutionMap f g).a.hom = biprod.map f.a.hom g.a.hom := rfl

theorem convolutionMap_id (E F : FixedTargetExtension C X) :
    convolutionMap (𝟙 E) (𝟙 F) = 𝟙 (convolutionObj E F) := by
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    change biprod.map (𝟙 E.A) (𝟙 F.A) = (𝟙 (E.A ⊞ F.A))
    apply biprod.hom_ext <;> simp
  · apply Iso.ext
    change convolutionMiddleMap (𝟙 E) (𝟙 F) = (𝟙 (convolutionPullback E F).obj)
    apply (convolutionPullback E F).square.hom_ext
    · simp only [convolutionMiddleMap_fst, FixedTargetExtension.id_b,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [convolutionMiddleMap_snd, FixedTargetExtension.id_b,
        Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem convolutionMap_comp {E E' E'' F F' F'' : FixedTargetExtension C X}
    (f : E ⟶ E') (f' : E' ⟶ E'') (g : F ⟶ F') (g' : F' ⟶ F'') :
    convolutionMap (f ≫ f') (g ≫ g') = convolutionMap f g ≫ convolutionMap f' g' := by
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    change biprod.map (f ≫ f').a.hom (g ≫ g').a.hom =
      biprod.map f.a.hom g.a.hom ≫ biprod.map f'.a.hom g'.a.hom
    simp only [FixedTargetExtension.comp_a, Iso.trans_hom]
    apply biprod.hom_ext <;> simp [Category.assoc]
  · apply Iso.ext
    change convolutionMiddleMap (f ≫ f') (g ≫ g') =
      convolutionMiddleMap f g ≫ convolutionMiddleMap f' g'
    apply (convolutionPullback E'' F'').square.hom_ext
    · simp only [Category.assoc, convolutionMiddleMap_fst,
        convolutionMiddleMap_fst_assoc, FixedTargetExtension.comp_b, Iso.trans_hom]
    · simp only [Category.assoc, convolutionMiddleMap_snd,
        convolutionMiddleMap_snd_assoc, FixedTargetExtension.comp_b, Iso.trans_hom]

/-- The actual convolution is a functor on the original given-X row groupoid. -/
def convolutionFunctor :
    FixedTargetExtension C X × FixedTargetExtension C X ⥤ FixedTargetExtension C X where
  obj p := convolutionObj p.1 p.2
  map {p q} f := convolutionMap f.1 f.2
  map_id p := by exact convolutionMap_id p.1 p.2
  map_comp f g := by exact convolutionMap_comp f.1 g.1 f.2 g.2

/-- Lift the original middle object into the unit-left convolution pullback,
with legs the quotient map and the identity. -/
def leftUnitMiddleInverse (E : FixedTargetExtension C X) :
    E.B ⟶ (convolutionPullback (unitRow X) E).obj :=
  (convolutionPullback (unitRow X) E).square.lift E.p (𝟙 E.B) (by simp [unitRow])

private theorem leftUnitMiddleInverse_fst (E : FixedTargetExtension C X) :
    leftUnitMiddleInverse E ≫ (convolutionPullback (unitRow X) E).fst = E.p :=
  (convolutionPullback (unitRow X) E).square.lift_fst _ _ _

private theorem leftUnitMiddleInverse_snd (E : FixedTargetExtension C X) :
    leftUnitMiddleInverse E ≫ (convolutionPullback (unitRow X) E).snd = 𝟙 E.B :=
  (convolutionPullback (unitRow X) E).square.lift_snd _ _ _

/-- Lift the original middle object into the unit-right convolution pullback,
with legs the identity and the quotient map. -/
def rightUnitMiddleInverse (E : FixedTargetExtension C X) :
    E.B ⟶ (convolutionPullback E (unitRow X)).obj :=
  (convolutionPullback E (unitRow X)).square.lift (𝟙 E.B) E.p (by simp [unitRow])

private theorem rightUnitMiddleInverse_fst (E : FixedTargetExtension C X) :
    rightUnitMiddleInverse E ≫ (convolutionPullback E (unitRow X)).fst = 𝟙 E.B :=
  (convolutionPullback E (unitRow X)).square.lift_fst _ _ _

private theorem rightUnitMiddleInverse_snd (E : FixedTargetExtension C X) :
    rightUnitMiddleInverse E ≫ (convolutionPullback E (unitRow X)).snd = E.p :=
  (convolutionPullback E (unitRow X)).square.lift_snd _ _ _

/-- The actual left unit middle Iso uses the second pullback projection. -/
def convolutionLeftUnitMiddleIso (E : FixedTargetExtension C X) :
    (convolutionPullback (unitRow X) E).obj ≅ E.B where
  hom := (convolutionPullback (unitRow X) E).snd
  inv := leftUnitMiddleInverse E
  hom_inv_id := by
    apply (convolutionPullback (unitRow X) E).square.hom_ext
    · rw [Category.assoc, leftUnitMiddleInverse_fst, Category.id_comp]
      simpa only [unitRow, Category.comp_id] using
        (convolutionPullback (unitRow X) E).square.w.symm
    · rw [Category.assoc, leftUnitMiddleInverse_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := by exact leftUnitMiddleInverse_snd E

/-- The actual right unit middle Iso uses the first pullback projection. -/
def convolutionRightUnitMiddleIso (E : FixedTargetExtension C X) :
    (convolutionPullback E (unitRow X)).obj ≅ E.B where
  hom := (convolutionPullback E (unitRow X)).fst
  inv := rightUnitMiddleInverse E
  hom_inv_id := by
    apply (convolutionPullback E (unitRow X)).square.hom_ext
    · rw [Category.assoc, rightUnitMiddleInverse_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, rightUnitMiddleInverse_snd, Category.id_comp]
      simpa only [unitRow, Category.comp_id] using
        (convolutionPullback E (unitRow X)).square.w
  inv_hom_id := by exact rightUnitMiddleInverse_fst E

/-- Left unit comparison at the same original given quotient. -/
def convolutionLeftUnitIso (E : FixedTargetExtension C X) :
    convolutionObj (unitRow X) E ≅ E := by
  let h : convolutionObj (unitRow X) E ⟶ E :=
    { a := (isoZeroBiprod (X := (0 : C)) (Y := E.A) (isZero_zero C)).symm
      b := convolutionLeftUnitMiddleIso E
      comm_i := by exact convolutionKernel_snd (unitRow X) E
      comm_p := by exact (convolutionPullback (unitRow X) E).square.w.symm }
  exact FixedTargetExtension.pairIso h

/-- Right unit comparison at the same original given quotient. -/
def convolutionRightUnitIso (E : FixedTargetExtension C X) :
    convolutionObj E (unitRow X) ≅ E := by
  let h : convolutionObj E (unitRow X) ⟶ E :=
    { a := (isoBiprodZero (X := E.A) (Y := (0 : C)) (isZero_zero C)).symm
      b := convolutionRightUnitMiddleIso E
      comm_i := by exact convolutionKernel_fst E (unitRow X)
      comm_p := by rfl }
  exact FixedTargetExtension.pairIso h

@[reassoc (attr := simp)]
theorem convolutionLeftUnitIso_middle (E : FixedTargetExtension C X) :
    (convolutionLeftUnitIso E).hom.b.hom = (convolutionPullback (unitRow X) E).snd := rfl

@[reassoc (attr := simp)]
theorem convolutionRightUnitIso_middle (E : FixedTargetExtension C X) :
    (convolutionRightUnitIso E).hom.b.hom = (convolutionPullback E (unitRow X)).fst := rfl

theorem convolutionLeftUnitIso_kernel (E : FixedTargetExtension C X) :
    (convolutionLeftUnitIso E).hom.a.hom = (biprod.snd : (0 : C) ⊞ E.A ⟶ E.A) := rfl

theorem convolutionRightUnitIso_kernel (E : FixedTargetExtension C X) :
    (convolutionRightUnitIso E).hom.a.hom = (biprod.fst : E.A ⊞ (0 : C) ⟶ E.A) := rfl

theorem convolutionLeftUnitIso_natural {E F : FixedTargetExtension C X} (f : E ⟶ F) :
    convolutionMap (𝟙 (unitRow X)) f ≫ (convolutionLeftUnitIso F).hom =
      (convolutionLeftUnitIso E).hom ≫ f := by
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    simp only [FixedTargetExtension.comp_a, Iso.trans_hom, convolutionMap_kernel,
      convolutionLeftUnitIso_kernel]
    exact biprod.map_snd _ _
  · apply Iso.ext
    simp only [FixedTargetExtension.comp_b, Iso.trans_hom, convolutionMap_middle,
      convolutionLeftUnitIso_middle]
    exact convolutionMiddleMap_snd _ _

theorem convolutionRightUnitIso_natural {E F : FixedTargetExtension C X} (f : E ⟶ F) :
    convolutionMap f (𝟙 (unitRow X)) ≫ (convolutionRightUnitIso F).hom =
      (convolutionRightUnitIso E).hom ≫ f := by
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    simp only [FixedTargetExtension.comp_a, Iso.trans_hom, convolutionMap_kernel,
      convolutionRightUnitIso_kernel]
    exact biprod.map_fst _ _
  · apply Iso.ext
    simp only [FixedTargetExtension.comp_b, Iso.trans_hom, convolutionMap_middle,
      convolutionRightUnitIso_middle]
    exact convolutionMiddleMap_fst _ _

/-- The actual outer first projection followed by the identity transport to the inner PB. -/
def leftRawOuter (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶ (convolutionPullback E F).obj :=
  (convolutionPullback (convolutionObj E F) G).fst ≫
    (convolutionObjMiddleIso E F).hom

/-- The actual outer second projection followed by the identity transport to the inner PB. -/
def rightRawOuter (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶ (convolutionPullback F G).obj :=
  (convolutionPullback E (convolutionObj F G)).snd ≫
    (convolutionObjMiddleIso F G).hom

private theorem leftRawOuter_quotient (E F G : FixedTargetExtension C X) :
    leftRawOuter E F G ≫ convolutionQuotient E F =
      (convolutionPullback (convolutionObj E F) G).fst ≫ (convolutionObj E F).p := by
  unfold leftRawOuter
  rw [Category.assoc, convolutionObj_middleIso_hom_p]

private theorem rightRawOuter_quotient (E F G : FixedTargetExtension C X) :
    rightRawOuter E F G ≫ convolutionQuotient F G =
      (convolutionPullback E (convolutionObj F G)).snd ≫ (convolutionObj F G).p := by
  unfold rightRawOuter
  rw [Category.assoc, convolutionObj_middleIso_hom_p]

/-- The first original middle projection out of a left-associated triple. -/
def leftTripleFirst (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶ E.B :=
  leftRawOuter E F G ≫ (convolutionPullback E F).fst

/-- The second original middle projection out of a left-associated triple. -/
def leftTripleSecond (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶ F.B :=
  leftRawOuter E F G ≫ (convolutionPullback E F).snd

/-- The third original middle projection out of a left-associated triple. -/
def leftTripleThird (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶ G.B :=
  (convolutionPullback (convolutionObj E F) G).snd

theorem leftTriple_second_third (E F G : FixedTargetExtension C X) :
    leftTripleSecond E F G ≫ F.p = leftTripleThird E F G ≫ G.p := by
  change (leftRawOuter E F G ≫ (convolutionPullback E F).snd) ≫ F.p =
    (convolutionPullback (convolutionObj E F) G).snd ≫ G.p
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q : (convolutionPullback E F).obj ⟶ X => leftRawOuter E F G ≫ q)
      (convolutionPullback E F).square.w.symm).trans
        ((leftRawOuter_quotient E F G).trans
          (convolutionPullback (convolutionObj E F) G).square.w))

theorem leftTriple_first_second (E F G : FixedTargetExtension C X) :
    leftTripleFirst E F G ≫ E.p = leftTripleSecond E F G ≫ F.p := by
  change (leftRawOuter E F G ≫ (convolutionPullback E F).fst) ≫ E.p =
    (leftRawOuter E F G ≫ (convolutionPullback E F).snd) ≫ F.p
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q : (convolutionPullback E F).obj ⟶ X => leftRawOuter E F G ≫ q)
      (convolutionPullback E F).square.w).trans (Category.assoc _ _ _).symm)

/-- Recover the middle pullback of the second and third rows from a
left-parenthesized triple using its second and third middle projections. -/
def associatorRightInner (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶ (convolutionPullback F G).obj :=
  (convolutionPullback F G).square.lift
    (leftTripleSecond E F G) (leftTripleThird E F G) (leftTriple_second_third E F G)

private theorem associatorRightInner_fst (E F G : FixedTargetExtension C X) :
    associatorRightInner E F G ≫ (convolutionPullback F G).fst = leftTripleSecond E F G :=
  (convolutionPullback F G).square.lift_fst _ _ _

private theorem associatorRightInner_snd (E F G : FixedTargetExtension C X) :
    associatorRightInner E F G ≫ (convolutionPullback F G).snd = leftTripleThird E F G :=
  (convolutionPullback F G).square.lift_snd _ _ _

private theorem associatorRightOuter_square (E F G : FixedTargetExtension C X) :
    leftTripleFirst E F G ≫ E.p =
      (associatorRightInner E F G ≫
        (convolutionObjMiddleIso F G).inv) ≫
          (convolutionObj F G).p := by
  have hp :
      (convolutionObjMiddleIso F G).inv ≫
        (convolutionObj F G).p = convolutionQuotient F G := by
    exact convolutionObj_middleIso_inv_p F G
  rw [Category.assoc, hp]
  change leftTripleFirst E F G ≫ E.p =
    associatorRightInner E F G ≫ ((convolutionPullback F G).fst ≫ F.p)
  rw [← Category.assoc, associatorRightInner_fst]
  exact leftTriple_first_second E F G

/-- The actual associator middle map regroups the same three original projections. -/
def convolutionAssocMiddle (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ⟶
      (convolutionPullback E (convolutionObj F G)).obj :=
  (convolutionPullback E (convolutionObj F G)).square.lift
    (leftTripleFirst E F G)
    (associatorRightInner E F G ≫
      (convolutionObjMiddleIso F G).inv)
    (by exact associatorRightOuter_square E F G)

private theorem convolutionAssocMiddle_outer_snd (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddle E F G ≫ rightRawOuter E F G = associatorRightInner E F G := by
  have hs : convolutionAssocMiddle E F G ≫
      (convolutionPullback E (convolutionObj F G)).snd =
      associatorRightInner E F G ≫
        (convolutionObjMiddleIso F G).inv :=
    (convolutionPullback E (convolutionObj F G)).square.lift_snd _ _ _
  unfold rightRawOuter
  rw [← Category.assoc, hs, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem convolutionAssocMiddle_first (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddle E F G ≫ (convolutionPullback E (convolutionObj F G)).fst =
      leftTripleFirst E F G :=
  (convolutionPullback E (convolutionObj F G)).square.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem convolutionAssocMiddle_second (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddle E F G ≫ rightRawOuter E F G ≫
        (convolutionPullback F G).fst = leftTripleSecond E F G := by
  rw [← Category.assoc, convolutionAssocMiddle_outer_snd, associatorRightInner_fst]

@[reassoc (attr := simp)]
theorem convolutionAssocMiddle_third (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddle E F G ≫ rightRawOuter E F G ≫
        (convolutionPullback F G).snd = leftTripleThird E F G := by
  rw [← Category.assoc, convolutionAssocMiddle_outer_snd, associatorRightInner_snd]

private theorem associatorLeftInner_square (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).fst ≫ E.p =
      (rightRawOuter E F G ≫ (convolutionPullback F G).fst) ≫ F.p := by
  exact (convolutionPullback E (convolutionObj F G)).square.w.trans
    ((rightRawOuter_quotient E F G).symm.trans (Category.assoc _ _ _).symm)

/-- Recover the middle pullback of the first and second rows from a
right-parenthesized triple using its first and second middle projections. -/
def associatorLeftInner (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶ (convolutionPullback E F).obj :=
  (convolutionPullback E F).square.lift
    (convolutionPullback E (convolutionObj F G)).fst
    (rightRawOuter E F G ≫ (convolutionPullback F G).fst)
    (by exact associatorLeftInner_square E F G)

private theorem associatorLeftInner_fst (E F G : FixedTargetExtension C X) :
    associatorLeftInner E F G ≫ (convolutionPullback E F).fst =
      (convolutionPullback E (convolutionObj F G)).fst :=
  (convolutionPullback E F).square.lift_fst _ _ _

private theorem associatorLeftInner_snd (E F G : FixedTargetExtension C X) :
    associatorLeftInner E F G ≫ (convolutionPullback E F).snd =
      rightRawOuter E F G ≫ (convolutionPullback F G).fst :=
  (convolutionPullback E F).square.lift_snd _ _ _

private theorem associatorLeftOuter_square (E F G : FixedTargetExtension C X) :
    (associatorLeftInner E F G ≫
      (convolutionObjMiddleIso E F).inv) ≫
        (convolutionObj E F).p =
      (rightRawOuter E F G ≫ (convolutionPullback F G).snd) ≫ G.p := by
  have hp :
      (convolutionObjMiddleIso E F).inv ≫
        (convolutionObj E F).p = convolutionQuotient E F := by
    exact convolutionObj_middleIso_inv_p E F
  rw [Category.assoc, hp]
  change associatorLeftInner E F G ≫ ((convolutionPullback E F).fst ≫ E.p) = _
  rw [← Category.assoc, associatorLeftInner_fst]
  exact (associatorLeftInner_square E F G).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q : (convolutionPullback F G).obj ⟶ X => rightRawOuter E F G ≫ q)
        (convolutionPullback F G).square.w).trans (Category.assoc _ _ _).symm))

/-- The inverse associator middle map regroups the same projections in the reverse order. -/
def convolutionAssocMiddleInv (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶
      (convolutionPullback (convolutionObj E F) G).obj :=
  (convolutionPullback (convolutionObj E F) G).square.lift
    (associatorLeftInner E F G ≫
      (convolutionObjMiddleIso E F).inv)
    (rightRawOuter E F G ≫ (convolutionPullback F G).snd)
    (by exact associatorLeftOuter_square E F G)

private theorem convolutionAssocMiddleInv_outer_fst (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddleInv E F G ≫ leftRawOuter E F G = associatorLeftInner E F G := by
  have hs : convolutionAssocMiddleInv E F G ≫
      (convolutionPullback (convolutionObj E F) G).fst =
      associatorLeftInner E F G ≫
        (convolutionObjMiddleIso E F).inv :=
    (convolutionPullback (convolutionObj E F) G).square.lift_fst _ _ _
  unfold leftRawOuter
  rw [← Category.assoc, hs, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem convolutionAssocMiddleInv_first (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddleInv E F G ≫ leftTripleFirst E F G =
      (convolutionPullback E (convolutionObj F G)).fst := by
  change convolutionAssocMiddleInv E F G ≫
    (leftRawOuter E F G ≫ (convolutionPullback E F).fst) = _
  rw [← Category.assoc, convolutionAssocMiddleInv_outer_fst, associatorLeftInner_fst]

@[reassoc (attr := simp)]
theorem convolutionAssocMiddleInv_second (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddleInv E F G ≫ leftTripleSecond E F G =
      rightRawOuter E F G ≫ (convolutionPullback F G).fst := by
  change convolutionAssocMiddleInv E F G ≫
    (leftRawOuter E F G ≫ (convolutionPullback E F).snd) = _
  rw [← Category.assoc, convolutionAssocMiddleInv_outer_fst, associatorLeftInner_snd]

@[reassoc (attr := simp)]
theorem convolutionAssocMiddleInv_third (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddleInv E F G ≫ leftTripleThird E F G =
      rightRawOuter E F G ≫ (convolutionPullback F G).snd :=
  (convolutionPullback (convolutionObj E F) G).square.lift_snd _ _ _

/-- Project a right-parenthesized convolution triple to the first original middle object. -/
def rightTripleFirst (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶ E.B :=
  (convolutionPullback E (convolutionObj F G)).fst

/-- Project a right-parenthesized convolution triple to the second original middle object. -/
def rightTripleSecond (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶ F.B :=
  rightRawOuter E F G ≫ (convolutionPullback F G).fst

/-- Project a right-parenthesized convolution triple to the third original middle object. -/
def rightTripleThird (E F G : FixedTargetExtension C X) :
    (convolutionPullback E (convolutionObj F G)).obj ⟶ G.B :=
  rightRawOuter E F G ≫ (convolutionPullback F G).snd

private theorem leftRawOuter_cancel {E F G : FixedTargetExtension C X} {W : C}
    (h k : W ⟶ (convolutionPullback (convolutionObj E F) G).obj)
    (hh : h ≫ leftRawOuter E F G = k ≫ leftRawOuter E F G) :
    h ≫ (convolutionPullback (convolutionObj E F) G).fst =
      k ≫ (convolutionPullback (convolutionObj E F) G).fst := by
  have back := congrArg
    (fun q : W ⟶ (convolutionPullback E F).obj => q ≫
      (convolutionObjMiddleIso E F).inv) hh
  simpa only [leftRawOuter, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using back

private theorem rightRawOuter_cancel {E F G : FixedTargetExtension C X} {W : C}
    (h k : W ⟶ (convolutionPullback E (convolutionObj F G)).obj)
    (hh : h ≫ rightRawOuter E F G = k ≫ rightRawOuter E F G) :
    h ≫ (convolutionPullback E (convolutionObj F G)).snd =
      k ≫ (convolutionPullback E (convolutionObj F G)).snd := by
  have back := congrArg
    (fun q : W ⟶ (convolutionPullback F G).obj => q ≫
      (convolutionObjMiddleIso F G).inv) hh
  simpa only [rightRawOuter, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using back

/-- Equality into the left triple pullback is detected by all three original middle legs. -/
theorem leftTriple_hom_ext (E F G : FixedTargetExtension C X) {W : C}
    {h k : W ⟶ (convolutionPullback (convolutionObj E F) G).obj}
    (h₁ : h ≫ leftTripleFirst E F G = k ≫ leftTripleFirst E F G)
    (h₂ : h ≫ leftTripleSecond E F G = k ≫ leftTripleSecond E F G)
    (h₃ : h ≫ leftTripleThird E F G = k ≫ leftTripleThird E F G) : h = k := by
  apply (convolutionPullback (convolutionObj E F) G).square.hom_ext
  · apply leftRawOuter_cancel h k
    apply (convolutionPullback E F).square.hom_ext
    · simpa only [Category.assoc, leftTripleFirst] using h₁
    · simpa only [Category.assoc, leftTripleSecond] using h₂
  · exact h₃

/-- Equality into the right triple pullback is detected by all three original middle legs. -/
theorem rightTriple_hom_ext (E F G : FixedTargetExtension C X) {W : C}
    {h k : W ⟶ (convolutionPullback E (convolutionObj F G)).obj}
    (h₁ : h ≫ rightTripleFirst E F G = k ≫ rightTripleFirst E F G)
    (h₂ : h ≫ rightTripleSecond E F G = k ≫ rightTripleSecond E F G)
    (h₃ : h ≫ rightTripleThird E F G = k ≫ rightTripleThird E F G) : h = k := by
  apply (convolutionPullback E (convolutionObj F G)).square.hom_ext
  · exact h₁
  · apply rightRawOuter_cancel h k
    apply (convolutionPullback F G).square.hom_ext
    · simpa only [Category.assoc, rightTripleSecond] using h₂
    · simpa only [Category.assoc, rightTripleThird] using h₃

/-- The associator is a genuine Iso of the independently chosen triple pullbacks. -/
def convolutionAssocMiddleIso (E F G : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E F) G).obj ≅
      (convolutionPullback E (convolutionObj F G)).obj where
  hom := convolutionAssocMiddle E F G
  inv := convolutionAssocMiddleInv E F G
  hom_inv_id := by
    apply leftTriple_hom_ext E F G
    · simp only [Category.assoc, convolutionAssocMiddleInv_first,
        convolutionAssocMiddle_first, Category.id_comp]
    · simp only [Category.assoc, convolutionAssocMiddleInv_second,
        convolutionAssocMiddle_second, Category.id_comp]
    · simp only [Category.assoc, convolutionAssocMiddleInv_third,
        convolutionAssocMiddle_third, Category.id_comp]
  inv_hom_id := by
    apply rightTriple_hom_ext E F G
    · simp only [rightTripleFirst, Category.assoc, convolutionAssocMiddle_first,
        convolutionAssocMiddleInv_first, Category.id_comp]
    · simp only [rightTripleSecond, Category.assoc, convolutionAssocMiddle_second,
        convolutionAssocMiddleInv_second, Category.id_comp]
    · simp only [rightTripleThird, Category.assoc, convolutionAssocMiddle_third,
        convolutionAssocMiddleInv_third, Category.id_comp]

private theorem leftKernelSource_eq (E F G : FixedTargetExtension C X) :
    ((convolutionObj E F).A ⊞ G.A) = ((E.A ⊞ F.A) ⊞ G.A) :=
  congrArg (fun Y : C => Y ⊞ G.A) (convolutionObj_kernel_eq E F)

private theorem rightKernelSource_eq (E F G : FixedTargetExtension C X) :
    (E.A ⊞ (convolutionObj F G).A) = (E.A ⊞ (F.A ⊞ G.A)) :=
  congrArg (fun Y : C => E.A ⊞ Y) (convolutionObj_kernel_eq F G)

private def leftCanonicalKernel (E F G : FixedTargetExtension C X) :
    (E.A ⊞ F.A) ⊞ G.A ⟶ (convolutionPullback (convolutionObj E F) G).obj :=
  (biprod.mapIso (eqToIso (convolutionObj_kernel_eq E F)) (Iso.refl G.A)).inv ≫
    convolutionKernel (convolutionObj E F) G

private def rightCanonicalKernel (E F G : FixedTargetExtension C X) :
    E.A ⊞ (F.A ⊞ G.A) ⟶ (convolutionPullback E (convolutionObj F G)).obj :=
  (biprod.mapIso (Iso.refl E.A) (eqToIso (convolutionObj_kernel_eq F G))).inv ≫
    convolutionKernel E (convolutionObj F G)

@[reassoc (attr := simp)]
private theorem leftCanonicalKernel_rawOuter (E F G : FixedTargetExtension C X) :
    leftCanonicalKernel E F G ≫ leftRawOuter E F G =
      (biprod.fst : (E.A ⊞ F.A) ⊞ G.A ⟶ E.A ⊞ F.A) ≫ convolutionKernel E F := by
  simp only [leftCanonicalKernel, leftRawOuter, Category.assoc,
    convolutionKernel_fst_assoc, convolutionObj_i_post_middle,
    biprod.mapIso, biprod.map_fst_assoc, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
private theorem leftCanonicalKernel_snd (E F G : FixedTargetExtension C X) :
    leftCanonicalKernel E F G ≫ (convolutionPullback (convolutionObj E F) G).snd =
      (biprod.snd : (E.A ⊞ F.A) ⊞ G.A ⟶ G.A) ≫ G.i := by
  simp only [leftCanonicalKernel, Category.assoc, convolutionKernel_snd,
    biprod.mapIso, biprod.map_snd_assoc, Iso.refl_inv, Category.id_comp]

@[reassoc (attr := simp)]
private theorem rightCanonicalKernel_fst (E F G : FixedTargetExtension C X) :
    rightCanonicalKernel E F G ≫ (convolutionPullback E (convolutionObj F G)).fst =
      (biprod.fst : E.A ⊞ (F.A ⊞ G.A) ⟶ E.A) ≫ E.i := by
  simp only [rightCanonicalKernel, Category.assoc, convolutionKernel_fst,
    biprod.mapIso, biprod.map_fst_assoc, Iso.refl_inv, Category.id_comp]

@[reassoc (attr := simp)]
private theorem rightCanonicalKernel_rawOuter (E F G : FixedTargetExtension C X) :
    rightCanonicalKernel E F G ≫ rightRawOuter E F G =
      (biprod.snd : E.A ⊞ (F.A ⊞ G.A) ⟶ F.A ⊞ G.A) ≫ convolutionKernel F G := by
  simp only [rightCanonicalKernel, rightRawOuter, Category.assoc,
    convolutionKernel_snd_assoc, convolutionObj_i_post_middle,
    biprod.mapIso, biprod.map_snd_assoc, Iso.inv_hom_id_assoc]

private theorem convolutionAssoc_kernel_canonical (E F G : FixedTargetExtension C X) :
    leftCanonicalKernel E F G ≫ convolutionAssocMiddle E F G =
      (biprod.associator E.A F.A G.A).hom ≫ rightCanonicalKernel E F G := by
  apply rightTriple_hom_ext E F G
  · simp [rightTripleFirst, leftTripleFirst, Category.assoc, biprod.associator,
    convolutionKernel_fst, rightCanonicalKernel_fst]
  · simp [rightTripleSecond, leftTripleSecond, Category.assoc, biprod.associator,
    convolutionKernel_snd, convolutionKernel_fst]
  · simp [rightTripleThird, leftTripleThird, Category.assoc, biprod.associator,
    convolutionKernel_snd, leftCanonicalKernel_snd]

omit [HasZeroObject C] [ExactCategory C] in
private theorem leftBiprodEqIso_inv_comp_heq {A B D Y : C} (p : A = B)
    (f : A ⊞ D ⟶ Y) :
    HEq ((biprod.mapIso (eqToIso p) (Iso.refl D)).inv ≫ f) f := by
  cases p
  simp only [eqToIso_refl, biprod.mapIso, Iso.refl_inv]
  apply heq_of_eq
  have hm : biprod.map (𝟙 A) (𝟙 D) = 𝟙 (A ⊞ D) := by
    apply biprod.hom_ext <;> simp
  rw [hm, Category.id_comp]

omit [HasZeroObject C] [ExactCategory C] in
private theorem rightBiprodEqIso_inv_comp_heq {A B D Y : C} (p : A = B)
    (f : D ⊞ A ⟶ Y) :
    HEq ((biprod.mapIso (Iso.refl D) (eqToIso p)).inv ≫ f) f := by
  cases p
  simp only [eqToIso_refl, biprod.mapIso, Iso.refl_inv]
  apply heq_of_eq
  have hm : biprod.map (𝟙 D) (𝟙 A) = 𝟙 (D ⊞ A) := by
    apply biprod.hom_ext <;> simp
  rw [hm, Category.id_comp]

/-- The associator kernel and middle maps preserve the actual kernel square. -/
theorem convolutionAssoc_kernel_square (E F G : FixedTargetExtension C X) :
    convolutionKernel (convolutionObj E F) G ≫ convolutionAssocMiddle E F G =
      (biprod.associator E.A F.A G.A).hom ≫ convolutionKernel E (convolutionObj F G) := by
  let ac : (E.A ⊞ F.A) ⊞ G.A ⟶ E.A ⊞ (F.A ⊞ G.A) :=
    (biprod.associator E.A F.A G.A).hom
  let ao : (convolutionObj E F).A ⊞ G.A ⟶ E.A ⊞ (convolutionObj F G).A :=
    (biprod.associator E.A F.A G.A).hom
  have ha : HEq ac ao := by rfl
  have hl : HEq (leftCanonicalKernel E F G)
      (convolutionKernel (convolutionObj E F) G) := by
    exact leftBiprodEqIso_inv_comp_heq (convolutionObj_kernel_eq E F)
      (convolutionKernel (convolutionObj E F) G)
  have hr : HEq (rightCanonicalKernel E F G)
      (convolutionKernel E (convolutionObj F G)) := by
    exact rightBiprodEqIso_inv_comp_heq (convolutionObj_kernel_eq F G)
      (convolutionKernel E (convolutionObj F G))
  have hleft := heq_comp (leftKernelSource_eq E F G).symm (rfl :
      (convolutionPullback (convolutionObj E F) G).obj =
        (convolutionPullback (convolutionObj E F) G).obj)
    (rfl : (convolutionPullback E (convolutionObj F G)).obj =
      (convolutionPullback E (convolutionObj F G)).obj) hl
    (show HEq (convolutionAssocMiddle E F G)
      (convolutionAssocMiddle E F G) from HEq.rfl)
  have hright := heq_comp (leftKernelSource_eq E F G).symm
    (rightKernelSource_eq E F G).symm
    (rfl : (convolutionPullback E (convolutionObj F G)).obj =
      (convolutionPullback E (convolutionObj F G)).obj) ha hr
  have hcanonical := heq_of_eq (convolutionAssoc_kernel_canonical E F G)
  exact eq_of_heq (hleft.symm.trans (hcanonical.trans hright))

theorem convolutionAssoc_quotient_square (E F G : FixedTargetExtension C X) :
    convolutionAssocMiddle E F G ≫ convolutionQuotient E (convolutionObj F G) =
      convolutionQuotient (convolutionObj E F) G := by
  change convolutionAssocMiddle E F G ≫
    ((convolutionPullback E (convolutionObj F G)).fst ≫ E.p) = _
  rw [← Category.assoc, convolutionAssocMiddle_first]
  change (leftRawOuter E F G ≫ (convolutionPullback E F).fst) ≫ E.p = _
  rw [Category.assoc]
  exact leftRawOuter_quotient E F G

/-- The actual row associator has the original biproduct kernel and pullback middle Iso. -/
def convolutionAssocIso (E F G : FixedTargetExtension C X) :
    convolutionObj (convolutionObj E F) G ≅ convolutionObj E (convolutionObj F G) := by
  let h : convolutionObj (convolutionObj E F) G ⟶ convolutionObj E (convolutionObj F G) :=
    { a := biprod.associator E.A F.A G.A
      b := convolutionAssocMiddleIso E F G
      comm_i := by exact convolutionAssoc_kernel_square E F G
      comm_p := by exact convolutionAssoc_quotient_square E F G }
  exact FixedTargetExtension.pairIso h

@[simp]
theorem convolutionAssocIso_kernel (E F G : FixedTargetExtension C X) :
    (convolutionAssocIso E F G).hom.a.hom = (biprod.associator E.A F.A G.A).hom := rfl

@[simp]
theorem convolutionAssocIso_middle (E F G : FixedTargetExtension C X) :
    (convolutionAssocIso E F G).hom.b.hom = convolutionAssocMiddle E F G := rfl

private def rawConvolutionRowMap {E F E' F' : FixedTargetExtension C X}
    (f : convolutionObj E F ⟶ convolutionObj E' F') :
    (convolutionPullback E F).obj ⟶ (convolutionPullback E' F').obj :=
  (convolutionObjMiddleIso E F).inv ≫
    f.b.hom ≫
      (convolutionObjMiddleIso E' F').hom

@[reassoc (attr := simp)]
private theorem rowMiddle_to_raw {E F E' F' : FixedTargetExtension C X}
    (f : convolutionObj E F ⟶ convolutionObj E' F') :
    f.b.hom ≫ (convolutionObjMiddleIso E' F').hom =
      (convolutionObjMiddleIso E F).hom ≫ rawConvolutionRowMap f := by
  simp only [rawConvolutionRowMap, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
private theorem convolutionMiddleMap_leftRawOuter {E F E' F' G G' :
    FixedTargetExtension C X} (f : convolutionObj E F ⟶ convolutionObj E' F')
    (g : G ⟶ G') :
    convolutionMiddleMap f g ≫ leftRawOuter E' F' G' =
      leftRawOuter E F G ≫ rawConvolutionRowMap f := by
  have h := congrArg
    (fun q : (convolutionPullback (convolutionObj E F) G).obj ⟶
      (convolutionObj E' F').B => q ≫ (convolutionObjMiddleIso E' F').hom)
    (convolutionMiddleMap_fst f g)
  simpa only [leftRawOuter, Category.assoc, rowMiddle_to_raw] using h

@[reassoc (attr := simp)]
private theorem convolutionMiddleMap_rightRawOuter {E E' F G F' G' :
    FixedTargetExtension C X} (f : E ⟶ E')
    (g : convolutionObj F G ⟶ convolutionObj F' G') :
    convolutionMiddleMap f g ≫ rightRawOuter E' F' G' =
      rightRawOuter E F G ≫ rawConvolutionRowMap g := by
  have h := congrArg
    (fun q : (convolutionPullback E (convolutionObj F G)).obj ⟶
      (convolutionObj F' G').B => q ≫ (convolutionObjMiddleIso F' G').hom)
    (convolutionMiddleMap_snd f g)
  simpa only [rightRawOuter, Category.assoc, rowMiddle_to_raw] using h

private theorem rawConvolutionRowMap_eq_of_heq {E F E' F' : FixedTargetExtension C X}
    (f : convolutionObj E F ⟶ convolutionObj E' F')
    (g : (convolutionPullback E F).obj ⟶ (convolutionPullback E' F').obj)
    (hfg : HEq f.b.hom g) : rawConvolutionRowMap f = g := by
  have h := (conj_eqToHom_iff_heq f.b.hom g (convolutionObj_middle_eq E F)
    (convolutionObj_middle_eq E' F')).2 hfg
  have hh : f.b.hom =
      (convolutionObjMiddleIso E F).hom ≫ g ≫ (convolutionObjMiddleIso E' F').inv := by
    simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToIso.inv] using h
  unfold rawConvolutionRowMap
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
private theorem rawConvolutionRowMap_map {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    rawConvolutionRowMap (convolutionMap f g) = convolutionMiddleMap f g := by
  apply rawConvolutionRowMap_eq_of_heq
  exact heq_of_eq (convolutionMap_middle f g)

@[simp]
private theorem rawConvolutionRowMap_assoc (E F G : FixedTargetExtension C X) :
    rawConvolutionRowMap (convolutionAssocIso E F G).hom = convolutionAssocMiddle E F G := by
  apply rawConvolutionRowMap_eq_of_heq
  exact heq_of_eq (convolutionAssocIso_middle E F G)

private theorem assocNatural_canonical {E E' F F' G G' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    convolutionMiddleMap (convolutionMap f g) h ≫ convolutionAssocMiddle E' F' G' =
      convolutionAssocMiddle E F G ≫ convolutionMiddleMap f (convolutionMap g h) := by
  apply rightTriple_hom_ext E' F' G'
  · have hL : (convolutionMiddleMap (convolutionMap f g) h ≫
          convolutionAssocMiddle E' F' G') ≫ rightTripleFirst E' F' G' =
        leftTripleFirst E F G ≫ f.b.hom := by
      simp only [rightTripleFirst, leftTripleFirst, Category.assoc,
        convolutionAssocMiddle_first, convolutionMiddleMap_leftRawOuter_assoc,
        rawConvolutionRowMap_map, convolutionMiddleMap_fst]
    have hR : (convolutionAssocMiddle E F G ≫
          convolutionMiddleMap f (convolutionMap g h)) ≫ rightTripleFirst E' F' G' =
        leftTripleFirst E F G ≫ f.b.hom := by
      simp only [rightTripleFirst, leftTripleFirst, Category.assoc, convolutionMiddleMap_fst,
        convolutionAssocMiddle_first_assoc]
    exact hL.trans hR.symm
  · have hL : (convolutionMiddleMap (convolutionMap f g) h ≫
          convolutionAssocMiddle E' F' G') ≫ rightTripleSecond E' F' G' =
        leftTripleSecond E F G ≫ g.b.hom := by
      simp only [rightTripleSecond, leftTripleSecond, Category.assoc,
        convolutionAssocMiddle_second, convolutionMiddleMap_leftRawOuter_assoc,
        rawConvolutionRowMap_map, convolutionMiddleMap_snd]
    have hR : (convolutionAssocMiddle E F G ≫
          convolutionMiddleMap f (convolutionMap g h)) ≫ rightTripleSecond E' F' G' =
        leftTripleSecond E F G ≫ g.b.hom := by
      simp only [rightTripleSecond, leftTripleSecond, Category.assoc,
        convolutionMiddleMap_rightRawOuter_assoc, rawConvolutionRowMap_map,
        convolutionMiddleMap_fst, convolutionAssocMiddle_second_assoc]
    exact hL.trans hR.symm
  · have hL : (convolutionMiddleMap (convolutionMap f g) h ≫
          convolutionAssocMiddle E' F' G') ≫ rightTripleThird E' F' G' =
        leftTripleThird E F G ≫ h.b.hom := by
      simp only [rightTripleThird, leftTripleThird, Category.assoc,
        convolutionAssocMiddle_third, convolutionMiddleMap_snd]
    have hR : (convolutionAssocMiddle E F G ≫
          convolutionMiddleMap f (convolutionMap g h)) ≫ rightTripleThird E' F' G' =
        leftTripleThird E F G ≫ h.b.hom := by
      simp only [rightTripleThird, leftTripleThird, Category.assoc,
        convolutionMiddleMap_rightRawOuter_assoc, rawConvolutionRowMap_map,
        convolutionMiddleMap_snd, convolutionAssocMiddle_third_assoc]
    exact hL.trans hR.symm

/-- Naturality follows from the three actual original middle projections. -/
theorem convolutionAssocIso_natural {E E' F F' G G' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    convolutionMap (convolutionMap f g) h ≫ (convolutionAssocIso E' F' G').hom =
      (convolutionAssocIso E F G).hom ≫ convolutionMap f (convolutionMap g h) := by
  let S := convolutionObj (convolutionObj E F) G
  let T := convolutionObj E' (convolutionObj F' G')
  let l : S ⟶ T := convolutionMap (convolutionMap f g) h ≫
    (convolutionAssocIso E' F' G').hom
  let r : S ⟶ T := (convolutionAssocIso E F G).hom ≫
    convolutionMap f (convolutionMap g h)
  let lc := convolutionMiddleMap (convolutionMap f g) h ≫ convolutionAssocMiddle E' F' G'
  let rc := convolutionAssocMiddle E F G ≫ convolutionMiddleMap f (convolutionMap g h)
  have hl : HEq l.b.hom lc := by
    have hm := heq_comp (convolutionObj_middle_eq (convolutionObj E F) G)
      (convolutionObj_middle_eq (convolutionObj E' F') G')
      (convolutionObj_middle_eq E' (convolutionObj F' G'))
      (heq_of_eq (convolutionMap_middle (convolutionMap f g) h))
      (heq_of_eq (convolutionAssocIso_middle E' F' G'))
    have hc := congrArg Iso.hom
      (FixedTargetExtension.comp_b (convolutionMap (convolutionMap f g) h)
        (convolutionAssocIso E' F' G').hom)
    exact (heq_of_eq hc).trans hm
  have hr : HEq r.b.hom rc := by
    have hm := heq_comp (convolutionObj_middle_eq (convolutionObj E F) G)
      (convolutionObj_middle_eq E (convolutionObj F G))
      (convolutionObj_middle_eq E' (convolutionObj F' G'))
      (heq_of_eq (convolutionAssocIso_middle E F G))
      (heq_of_eq (convolutionMap_middle f (convolutionMap g h)))
    have hc := congrArg Iso.hom
      (FixedTargetExtension.comp_b (convolutionAssocIso E F G).hom
        (convolutionMap f (convolutionMap g h)))
    exact (heq_of_eq hc).trans hm
  have hb : l.b.hom = r.b.hom :=
    eq_of_heq (hl.trans ((heq_of_eq (assocNatural_canonical f g h)).trans hr.symm))
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    apply Fork.IsLimit.hom_ext (rowKernelPresentation T).kernelIsLimit
    exact l.comm_i.symm.trans ((congrArg (S.i ≫ ·) hb).trans r.comm_i)
  · exact Iso.ext hb

private theorem coherenceRowMiddle_eq_of_heq {E F E' F' : FixedTargetExtension C X}
    (f g : convolutionObj E F ⟶ convolutionObj E' F')
    (fc gc : (convolutionPullback E F).obj ⟶ (convolutionPullback E' F').obj)
    (hf : HEq f.b.hom fc) (hg : HEq g.b.hom gc) (h : fc = gc) : f = g := by
  have hb : f.b.hom = g.b.hom := eq_of_heq (hf.trans ((heq_of_eq h).trans hg.symm))
  apply FixedTargetExtension.Hom.ext
  · apply Iso.ext
    apply Fork.IsLimit.hom_ext (rowKernelPresentation (convolutionObj E' F')).kernelIsLimit
    exact f.comm_i.symm.trans
      ((congrArg ((convolutionObj E F).i ≫ ·) hb).trans g.comm_i)
  · exact Iso.ext hb

@[reassoc]
private theorem coherenceLeftUnit_middle (E : FixedTargetExtension C X) :
    (convolutionObjMiddleIso (unitRow X) E).inv ≫
      (convolutionLeftUnitIso E).hom.b.hom =
        (convolutionPullback (unitRow X) E).snd := by
  have h := (conj_eqToHom_iff_heq (convolutionLeftUnitIso E).hom.b.hom
    (convolutionPullback (unitRow X) E).snd
    (convolutionObj_middle_eq (unitRow X) E) (rfl : E.B = E.B)).2
      (heq_of_eq (convolutionLeftUnitIso_middle E))
  have h₀ : (convolutionLeftUnitIso E).hom.b.hom =
      (convolutionObjMiddleIso (unitRow X) E).hom ≫
        (convolutionPullback (unitRow X) E).snd := by
    simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToHom_refl,
      Category.comp_id] using h
  rw [h₀]
  simp only [Iso.inv_hom_id_assoc]

@[reassoc]
private theorem coherenceRightUnit_middle (E : FixedTargetExtension C X) :
    (convolutionObjMiddleIso E (unitRow X)).inv ≫
      (convolutionRightUnitIso E).hom.b.hom =
        (convolutionPullback E (unitRow X)).fst := by
  have h := (conj_eqToHom_iff_heq (convolutionRightUnitIso E).hom.b.hom
    (convolutionPullback E (unitRow X)).fst
    (convolutionObj_middle_eq E (unitRow X)) (rfl : E.B = E.B)).2
      (heq_of_eq (convolutionRightUnitIso_middle E))
  have h₀ : (convolutionRightUnitIso E).hom.b.hom =
      (convolutionObjMiddleIso E (unitRow X)).hom ≫
        (convolutionPullback E (unitRow X)).fst := by
    simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToHom_refl,
      Category.comp_id] using h
  rw [h₀]
  simp only [Iso.inv_hom_id_assoc]

private theorem coherenceRightUnit_post (E F : FixedTargetExtension C X) :
    (convolutionPullback (convolutionObj E (unitRow X)) F).fst ≫
      (convolutionRightUnitIso E).hom.b.hom = leftTripleFirst E (unitRow X) F := by
  change (convolutionPullback (convolutionObj E (unitRow X)) F).fst ≫
    (convolutionRightUnitIso E).hom.b.hom = leftRawOuter E (unitRow X) F ≫
      (convolutionPullback E (unitRow X)).fst
  have h := (conj_eqToHom_iff_heq (convolutionRightUnitIso E).hom.b.hom
    (convolutionPullback E (unitRow X)).fst
    (convolutionObj_middle_eq E (unitRow X)) (rfl : E.B = E.B)).2
      (heq_of_eq (convolutionRightUnitIso_middle E))
  have h₀ : (convolutionRightUnitIso E).hom.b.hom =
      (convolutionObjMiddleIso E (unitRow X)).hom ≫
        (convolutionPullback E (unitRow X)).fst := by
    simpa only [convolutionObjMiddleIso, eqToIso.hom, eqToHom_refl,
      Category.comp_id] using h
  rw [h₀]
  simpa only [leftRawOuter] using
    (Category.assoc
      (convolutionPullback (convolutionObj E (unitRow X)) F).fst
      (convolutionObjMiddleIso E (unitRow X)).hom
      (convolutionPullback E (unitRow X)).fst).symm

private theorem coherence_triangle_canonical (E F : FixedTargetExtension C X) :
    convolutionAssocMiddle E (unitRow X) F ≫
        convolutionMiddleMap (𝟙 E) (convolutionLeftUnitIso F).hom =
      convolutionMiddleMap (convolutionRightUnitIso E).hom (𝟙 F) := by
  apply (convolutionPullback E F).square.hom_ext
  · simp only [Category.assoc, convolutionMiddleMap_fst,
      FixedTargetExtension.id_b, Iso.refl_hom, Category.comp_id,
      convolutionAssocMiddle_first]
    exact (coherenceRightUnit_post E F).symm
  · have h := coherenceLeftUnit_middle F
    have hPost : (convolutionLeftUnitIso F).hom.b.hom =
        (convolutionObjMiddleIso (unitRow X) F).hom ≫
          (convolutionPullback (unitRow X) F).snd := by
      have h₀ := congrArg
        (fun k : (convolutionPullback (unitRow X) F).obj ⟶ F.B =>
          (convolutionObjMiddleIso (unitRow X) F).hom ≫ k) h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h₀
    simp only [Category.assoc, convolutionMiddleMap_snd,
      FixedTargetExtension.id_b, Iso.refl_hom, Category.comp_id]
    rw [hPost]
    simpa only [rightRawOuter, leftTripleThird, Category.assoc] using
      (convolutionAssocMiddle_third E (unitRow X) F)

/-- The convolution unit triangle holds on the original row and middle maps. -/
theorem convolution_triangle (E F : FixedTargetExtension C X) :
    (convolutionAssocIso E (unitRow X) F).hom ≫
        convolutionMap (𝟙 E) (convolutionLeftUnitIso F).hom =
      convolutionMap (convolutionRightUnitIso E).hom (𝟙 F) := by
  let A := convolutionObj E (unitRow X)
  let B := convolutionObj (unitRow X) F
  let L := (convolutionAssocIso E (unitRow X) F).hom ≫
    convolutionMap (𝟙 E) (convolutionLeftUnitIso F).hom
  let R := convolutionMap (convolutionRightUnitIso E).hom (𝟙 F)
  let lc := convolutionAssocMiddle E (unitRow X) F ≫
    convolutionMiddleMap (𝟙 E) (convolutionLeftUnitIso F).hom
  let rc := convolutionMiddleMap (convolutionRightUnitIso E).hom (𝟙 F)
  have hL : HEq L.b.hom lc := by
    have h₀ := heq_comp (convolutionObj_middle_eq A F)
      (convolutionObj_middle_eq E B) (convolutionObj_middle_eq E F)
      (heq_of_eq (convolutionAssocIso_middle E (unitRow X) F))
      (heq_of_eq (convolutionMap_middle (𝟙 E) (convolutionLeftUnitIso F).hom))
    have hComp := congrArg Iso.hom
      (FixedTargetExtension.comp_b (convolutionAssocIso E (unitRow X) F).hom
        (convolutionMap (𝟙 E) (convolutionLeftUnitIso F).hom))
    exact (heq_of_eq hComp).trans h₀
  have hR : HEq R.b.hom rc :=
    heq_of_eq (convolutionMap_middle (convolutionRightUnitIso E).hom (𝟙 F))
  exact coherenceRowMiddle_eq_of_heq L R lc rc hL hR (coherence_triangle_canonical E F)

@[reassoc (attr := simp)]
private theorem coherenceAssoc_leftRawOuter (E F G H : FixedTargetExtension C X) :
    convolutionAssocMiddle (convolutionObj E F) G H ≫
      leftRawOuter E F (convolutionObj G H) =
    leftRawOuter (convolutionObj E F) G H ≫ leftRawOuter E F G := by
  have h := congrArg
    (fun k : (convolutionPullback (convolutionObj (convolutionObj E F) G) H).obj ⟶
        (convolutionObj E F).B => k ≫ (convolutionObjMiddleIso E F).hom)
    (convolutionAssocMiddle_first (convolutionObj E F) G H)
  simpa only [leftRawOuter, leftTripleFirst, Category.assoc] using h

@[reassoc (attr := simp)]
private theorem coherenceAssoc_innerRawOuter (E F G H : FixedTargetExtension C X) :
    convolutionAssocMiddle E (convolutionObj F G) H ≫
      rightRawOuter E (convolutionObj F G) H ≫ leftRawOuter F G H =
    leftRawOuter E (convolutionObj F G) H ≫ rightRawOuter E F G := by
  have h := congrArg
    (fun k : (convolutionPullback (convolutionObj E (convolutionObj F G)) H).obj ⟶
      (convolutionObj F G).B => k ≫ (convolutionObjMiddleIso F G).hom)
    (convolutionAssocMiddle_second E (convolutionObj F G) H)
  simpa only [leftRawOuter, rightRawOuter, leftTripleSecond, Category.assoc] using h

@[reassoc (attr := simp)]
private theorem coherenceAssoc_lastRawOuter (E F G H : FixedTargetExtension C X) :
    convolutionAssocMiddle E F (convolutionObj G H) ≫
      rightRawOuter E F (convolutionObj G H) ≫ rightRawOuter F G H =
    rightRawOuter (convolutionObj E F) G H := by
  have h := congrArg
    (fun k : (convolutionPullback (convolutionObj E F) (convolutionObj G H)).obj ⟶
      (convolutionObj G H).B => k ≫ (convolutionObjMiddleIso G H).hom)
    (convolutionAssocMiddle_third E F (convolutionObj G H))
  simpa only [rightRawOuter, leftTripleThird, Category.assoc] using h

private theorem coherence_pentagon_canonical (E F G H : FixedTargetExtension C X) :
    convolutionMiddleMap (convolutionAssocIso E F G).hom (𝟙 H) ≫
        convolutionAssocMiddle E (convolutionObj F G) H ≫
        convolutionMiddleMap (𝟙 E) (convolutionAssocIso F G H).hom =
      convolutionAssocMiddle (convolutionObj E F) G H ≫
        convolutionAssocMiddle E F (convolutionObj G H) := by
  apply rightTriple_hom_ext E F (convolutionObj G H)
  · simp [rightTripleFirst, leftTripleFirst, Category.assoc, rawConvolutionRowMap_assoc]
  · simp [rightTripleSecond, leftTripleFirst, leftTripleSecond, Category.assoc,
    rawConvolutionRowMap_assoc]
  · apply (cancel_mono (convolutionObjMiddleIso G H).hom).mp
    have hNative :
      convolutionMiddleMap (convolutionAssocIso E F G).hom (𝟙 H) ≫
          convolutionAssocMiddle E (convolutionObj F G) H ≫
          convolutionMiddleMap (𝟙 E) (convolutionAssocIso F G H).hom ≫
          rightRawOuter E F (convolutionObj G H) ≫ rightRawOuter F G H =
        convolutionAssocMiddle (convolutionObj E F) G H ≫
          convolutionAssocMiddle E F (convolutionObj G H) ≫
          rightRawOuter E F (convolutionObj G H) ≫ rightRawOuter F G H := by
      apply (convolutionPullback G H).square.hom_ext
      · simp [Category.assoc, leftTripleSecond, leftTripleThird, rawConvolutionRowMap_assoc,
        coherenceAssoc_lastRawOuter]
      · simp [Category.assoc, leftTripleThird, rawConvolutionRowMap_assoc,
        coherenceAssoc_lastRawOuter]
    simpa only [rightTripleThird, rightRawOuter, Category.assoc] using hNative

/-- The convolution pentagon is equality on all four original middle projections. -/
theorem convolution_pentagon (E F G H : FixedTargetExtension C X) :
    convolutionMap (convolutionAssocIso E F G).hom (𝟙 H) ≫
        (convolutionAssocIso E (convolutionObj F G) H).hom ≫
        convolutionMap (𝟙 E) (convolutionAssocIso F G H).hom =
      (convolutionAssocIso (convolutionObj E F) G H).hom ≫
        (convolutionAssocIso E F (convolutionObj G H)).hom := by
  let A := convolutionObj E F
  let B := convolutionObj F G
  let C1 := convolutionObj G H
  let L := convolutionMap (convolutionAssocIso E F G).hom (𝟙 H) ≫
    (convolutionAssocIso E B H).hom ≫
    convolutionMap (𝟙 E) (convolutionAssocIso F G H).hom
  let R := (convolutionAssocIso A G H).hom ≫ (convolutionAssocIso E F C1).hom
  let lc := convolutionMiddleMap (convolutionAssocIso E F G).hom (𝟙 H) ≫
    convolutionAssocMiddle E B H ≫
      convolutionMiddleMap (𝟙 E) (convolutionAssocIso F G H).hom
  let rc := convolutionAssocMiddle A G H ≫ convolutionAssocMiddle E F C1
  have hL : HEq L.b.hom lc := by
    have h₂ := heq_comp (convolutionObj_middle_eq (convolutionObj E B) H)
      (convolutionObj_middle_eq E (convolutionObj B H))
      (convolutionObj_middle_eq E (convolutionObj F C1))
      (heq_of_eq (convolutionAssocIso_middle E B H))
      (heq_of_eq (convolutionMap_middle (𝟙 E) (convolutionAssocIso F G H).hom))
    have h₁ := heq_comp (convolutionObj_middle_eq (convolutionObj A G) H)
      (convolutionObj_middle_eq (convolutionObj E B) H)
      (convolutionObj_middle_eq E (convolutionObj F C1))
      (heq_of_eq (convolutionMap_middle (convolutionAssocIso E F G).hom (𝟙 H))) h₂
    have hComp : L.b.hom =
        (convolutionMap (convolutionAssocIso E F G).hom (𝟙 H)).b.hom ≫
          (convolutionAssocIso E B H).hom.b.hom ≫
          (convolutionMap (𝟙 E) (convolutionAssocIso F G H).hom).b.hom := by
      simp only [L, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hComp).trans h₁
  have hR : HEq R.b.hom rc := by
    have h₀ := heq_comp (convolutionObj_middle_eq (convolutionObj A G) H)
      (convolutionObj_middle_eq A C1) (convolutionObj_middle_eq E (convolutionObj F C1))
      (heq_of_eq (convolutionAssocIso_middle A G H))
      (heq_of_eq (convolutionAssocIso_middle E F C1))
    have hComp := congrArg Iso.hom
      (FixedTargetExtension.comp_b (convolutionAssocIso A G H).hom
        (convolutionAssocIso E F C1).hom)
    exact (heq_of_eq hComp).trans h₀
  exact coherenceRowMiddle_eq_of_heq L R lc rc hL hR (coherence_pentagon_canonical E F G H)

/-- The convolution tensor data are the actual chosen pullbacks and row comparison Isos. -/
@[instance_reducible]
def convolutionMonoidalStruct : MonoidalCategoryStruct (FixedTargetExtension C X) where
  tensorObj := convolutionObj
  whiskerLeft E {_F _G} f := convolutionMap (𝟙 E) f
  whiskerRight {_E _F} f G := convolutionMap f (𝟙 G)
  tensorHom {_E _E' _F _F'} f g := convolutionMap f g
  tensorUnit := unitRow X
  associator := convolutionAssocIso
  leftUnitor := convolutionLeftUnitIso
  rightUnitor := convolutionRightUnitIso

attribute [local instance] convolutionMonoidalStruct

/-- The original given-X row convolution satisfies the full monoidal coherence axioms. -/
@[instance_reducible]
def convolutionMonoidal : MonoidalCategory (FixedTargetExtension C X) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun E F => convolutionMap_id E F)
    (id_tensorHom := by intro _E _F _G _f; rfl)
    (tensorHom_id := by intro _E _F _f _G; rfl)
    (tensorHom_comp_tensorHom := by
      intro _E _E' _E'' _F _F' _F'' f g f' g'
      exact (convolutionMap_comp f f' g g').symm)
    (associator_naturality := by
      intro E F G E' F' G' f g h
      exact convolutionAssocIso_natural f g h)
    (leftUnitor_naturality := by
      intro E F f
      exact convolutionLeftUnitIso_natural f)
    (rightUnitor_naturality := by
      intro E F f
      exact convolutionRightUnitIso_natural f)
    (pentagon := convolution_pentagon)
    (triangle := convolution_triangle)

end AlgebraicKTheory.AuxiliaryExtension

end


/-!
# Actual product of auxiliary stabilized maps

The action comparison retains the original two stabilizers. Its middle maps
are characterized by the four original T/E/U/F projections. The quotient
relation is the existing stabilizer-isomorphism relation of L.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

omit [HasZeroObject C] [ExactCategory C] in
/-- The explicit biproduct exchange preserves all four original summands. -/
def exchangeIso (A B D E : C) : (A ⊞ B) ⊞ (D ⊞ E) ≅ (A ⊞ D) ⊞ (B ⊞ E) where
  hom := biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  inv := biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  hom_inv_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [Category.assoc]

/-- The first target leg uses the original T summand and E middle projection. -/
def actionConvolutionFirst (T U : Core C) (E F : FixedTargetExtension C X) :
    (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ⟶ T.of ⊞ E.B :=
  biprod.lift (biprod.fst ≫ biprod.fst)
    (biprod.snd ≫ (convolutionPullback E F).fst)

/-- The second target leg uses the original U summand and F middle projection. -/
def actionConvolutionSecond (T U : Core C) (E F : FixedTargetExtension C X) :
    (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ⟶ U.of ⊞ F.B :=
  biprod.lift (biprod.fst ≫ biprod.snd)
    (biprod.snd ≫ (convolutionPullback E F).snd)

private theorem actionConvolution_square (T U : Core C) (E F : FixedTargetExtension C X) :
    (actionConvolutionFirst T U E F ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv) ≫
      (FixedTargetExtension.leftSumObj T E).p =
      (actionConvolutionSecond T U E F ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).inv) ≫
      (FixedTargetExtension.leftSumObj U F).p := by
  have hpE :
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv ≫
        (FixedTargetExtension.leftSumObj T E).p =
      (biprod.snd : T.of ⊞ E.B ⟶ E.B) ≫ E.p := by
    exact leftSumObj_middleIso_inv_p T E
  have hpF :
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).inv ≫
        (FixedTargetExtension.leftSumObj U F).p =
      (biprod.snd : U.of ⊞ F.B ⟶ F.B) ≫ F.p := by
    exact leftSumObj_middleIso_inv_p U F
  rw [Category.assoc, hpE, Category.assoc, hpF]
  simp only [actionConvolutionFirst, actionConvolutionSecond, biprod.lift_snd_assoc,
    Category.assoc]
  exact congrArg (biprod.snd ≫ ·) (convolutionPullback E F).square.w

/-- The actual forward comparison into the stabilized-row pullback. -/
def actionConvolutionMiddle (T U : Core C) (E F : FixedTargetExtension C X) :
    (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ⟶
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).obj :=
  (convolutionPullback (FixedTargetExtension.leftSumObj T E)
    (FixedTargetExtension.leftSumObj U F)).square.lift
      (actionConvolutionFirst T U E F ≫
        (eqToIso (by exact leftSumObj_middle_eq T E) :
          (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv)
      (actionConvolutionSecond T U E F ≫
        (eqToIso (by exact leftSumObj_middle_eq U F) :
          (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).inv)
      (by exact actionConvolution_square T U E F)

@[reassoc (attr := simp)]
theorem actionConvolutionMiddle_first (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst = actionConvolutionFirst T U E F ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv :=
  (convolutionPullback (FixedTargetExtension.leftSumObj T E)
    (FixedTargetExtension.leftSumObj U F)).square.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem actionConvolutionMiddle_second (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd = actionConvolutionSecond T U E F ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).inv :=
  (convolutionPullback (FixedTargetExtension.leftSumObj T E)
    (FixedTargetExtension.leftSumObj U F)).square.lift_snd _ _ _

/-- Extract the two stabilizer coordinates from the stabilized convolution
pullback as a morphism to their original biproduct. -/
def actionInverseKernel (T U : Core C) (E F : FixedTargetExtension C X) :
    (convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).obj ⟶ T.of ⊞ U.of :=
  biprod.lift
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.fst)
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.fst)

private theorem actionInverseKernel_fst (T U : Core C) (E F : FixedTargetExtension C X) :
    actionInverseKernel T U E F ≫ biprod.fst =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.fst :=
  biprod.lift_fst _ _

private theorem actionInverseKernel_snd (T U : Core C) (E F : FixedTargetExtension C X) :
    actionInverseKernel T U E F ≫ biprod.snd =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.fst :=
  biprod.lift_snd _ _

private theorem actionInverseMiddle_square (T U : Core C)
    (E F : FixedTargetExtension C X) :
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫ biprod.snd) ≫ E.p =
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫ biprod.snd) ≫ F.p := by
  let P := convolutionPullback (FixedTargetExtension.leftSumObj T E)
    (FixedTargetExtension.leftSumObj U F)
  have hE := congrArg
    (fun q : (FixedTargetExtension.leftSumObj T E).B ⟶ X => P.fst ≫ q)
    (leftSumObj_middleIso_hom_p T E)
  have hF := congrArg
    (fun q : (FixedTargetExtension.leftSumObj U F).B ⟶ X => P.snd ≫ q)
    (leftSumObj_middleIso_hom_p U F)
  simpa only [Category.assoc] using hE.trans (P.square.w.trans hF.symm)

/-- Map the stabilized convolution pullback to the original row pullback
by projecting away the stabilizer coordinate on each middle leg. -/
def actionInverseMiddle (T U : Core C) (E F : FixedTargetExtension C X) :
    (convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).obj ⟶ (convolutionPullback E F).obj :=
  (convolutionPullback E F).square.lift
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.snd)
    ((convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.snd)
    (by exact actionInverseMiddle_square T U E F)

private theorem actionInverseMiddle_fst (T U : Core C) (E F : FixedTargetExtension C X) :
    actionInverseMiddle T U E F ≫ (convolutionPullback E F).fst =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.snd :=
  (convolutionPullback E F).square.lift_fst _ _ _

private theorem actionInverseMiddle_snd (T U : Core C) (E F : FixedTargetExtension C X) :
    actionInverseMiddle T U E F ≫ (convolutionPullback E F).snd =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.snd :=
  (convolutionPullback E F).square.lift_snd _ _ _

@[reassoc]
private theorem actionConvolutionMiddle_first_native (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (leftSumObj_middle_eq T E)).hom = actionConvolutionFirst T U E F := by
  rw [← Category.assoc, actionConvolutionMiddle_first, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

@[reassoc]
private theorem actionConvolutionMiddle_second_native (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (leftSumObj_middle_eq U F)).hom = actionConvolutionSecond T U E F := by
  rw [← Category.assoc, actionConvolutionMiddle_second, Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

@[reassoc]
private theorem leftSumMap_middle_post {T T' : Core C} (t : T ⟶ T')
    {E E' : FixedTargetExtension C X} (f : E ⟶ E') :
    (FixedTargetExtension.leftSumMap t f).b.hom ≫
      (eqToIso (leftSumObj_middle_eq T' E')).hom =
    (eqToIso (leftSumObj_middle_eq T E)).hom ≫ biprod.map t.iso.hom f.b.hom := by
  have h := (conj_eqToHom_iff_heq (FixedTargetExtension.leftSumMap t f).b.hom
    (biprod.map t.iso.hom f.b.hom) (leftSumObj_middle_eq T E)
    (leftSumObj_middle_eq T' E')).2
      (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom t f))
  have hh : (FixedTargetExtension.leftSumMap t f).b.hom =
      (eqToIso (leftSumObj_middle_eq T E)).hom ≫ biprod.map t.iso.hom f.b.hom ≫
        (eqToIso (leftSumObj_middle_eq T' E')).inv := by
    simpa only [eqToIso.hom, eqToIso.inv] using h
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse comparison extracts the two summands and the original pullback. -/
def actionConvolutionMiddleInv (T U : Core C) (E F : FixedTargetExtension C X) :
    (convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).obj ⟶
        (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj :=
  biprod.lift (actionInverseKernel T U E F) (actionInverseMiddle T U E F)

private theorem actionConvolutionMiddleInv_fst (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.fst = actionInverseKernel T U E F :=
  biprod.lift_fst _ _

private theorem actionConvolutionMiddleInv_snd (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.snd = actionInverseMiddle T U E F :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
theorem actionConvolutionMiddleInv_T (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.fst ≫ biprod.fst =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.fst := by
  rw [← Category.assoc, actionConvolutionMiddleInv_fst, actionInverseKernel_fst]

@[reassoc (attr := simp)]
theorem actionConvolutionMiddleInv_U (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.fst ≫ biprod.snd =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.fst := by
  rw [← Category.assoc, actionConvolutionMiddleInv_fst, actionInverseKernel_snd]

@[reassoc (attr := simp)]
theorem actionConvolutionMiddleInv_E (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.snd ≫ (convolutionPullback E F).fst =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (by exact leftSumObj_middle_eq T E) :
        (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom ≫
        biprod.snd := by
  rw [← Category.assoc, actionConvolutionMiddleInv_snd, actionInverseMiddle_fst]

@[reassoc (attr := simp)]
theorem actionConvolutionMiddleInv_F (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddleInv T U E F ≫ biprod.snd ≫ (convolutionPullback E F).snd =
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (by exact leftSumObj_middle_eq U F) :
        (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom ≫
        biprod.snd := by
  rw [← Category.assoc, actionConvolutionMiddleInv_snd, actionInverseMiddle_snd]

/-- The actual stabilization/convolution comparison is an Iso of middle objects. -/
def actionConvolutionMiddleIso (T U : Core C) (E F : FixedTargetExtension C X) :
    (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ≅
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).obj where
  hom := actionConvolutionMiddle T U E F
  inv := actionConvolutionMiddleInv T U E F
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;>
        simp [Category.assoc, actionConvolutionMiddleInv, actionInverseKernel,
          actionConvolutionFirst, actionConvolutionSecond]
    · apply (convolutionPullback E F).square.hom_ext <;>
        simp [Category.assoc, actionConvolutionMiddleInv, actionInverseMiddle,
          actionConvolutionFirst, actionConvolutionSecond]
  inv_hom_id := by
    apply (convolutionPullback (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F)).square.hom_ext
    · apply (cancel_mono (eqToIso (by exact leftSumObj_middle_eq T E) :
      (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).hom).mp
      simp only [Category.assoc, actionConvolutionMiddle_first_native, Category.id_comp]
      apply biprod.hom_ext <;>
        simp [Category.assoc, actionConvolutionMiddleInv, actionInverseKernel,
          actionInverseMiddle, actionConvolutionFirst]
    · apply (cancel_mono (eqToIso (by exact leftSumObj_middle_eq U F) :
      (FixedTargetExtension.leftSumObj U F).B ≅ (U.of ⊞ F.B)).hom).mp
      simp only [Category.assoc, actionConvolutionMiddle_second_native, Category.id_comp]
      apply biprod.hom_ext <;>
        simp [Category.assoc, actionConvolutionMiddleInv, actionInverseKernel,
          actionInverseMiddle, actionConvolutionSecond]


omit [HasZeroObject C] [ExactCategory C] in
private theorem actionBiprodEqIso_inv_comp_heq {A B D H Y : C}
    (p : A = B) (q : D = H) (f : A ⊞ D ⟶ Y) :
    HEq ((biprod.mapIso (eqToIso p) (eqToIso q)).inv ≫ f) f := by
  cases p
  cases q
  simp only [eqToIso_refl, biprod.mapIso, Iso.refl_inv]
  apply heq_of_eq
  have hm : biprod.map (𝟙 A) (𝟙 D) = 𝟙 (A ⊞ D) := by
    apply biprod.hom_ext <;> simp
  rw [hm, Category.id_comp]

private theorem actionTensor_kernel_eq (T U : Core C) (E F : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).A) =
      ((T.of ⊞ U.of) ⊞ (E.A ⊞ F.A)) := by rfl

private theorem actionTensor_i_heq (T U : Core C) (E F : FixedTargetExtension C X) :
    HEq (FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).i
      (biprod.map (𝟙 (T.of ⊞ U.of)) (convolutionKernel E F)) := by rfl

private theorem actionTensor_p_heq (T U : Core C) (E F : FixedTargetExtension C X) :
    HEq (FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).p
      ((biprod.snd : (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ⟶
        (convolutionPullback E F).obj) ≫ convolutionQuotient E F) := by rfl

private def actionCanonicalKernel (T U : Core C) (E F : FixedTargetExtension C X) :
    (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A) ⟶
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).obj :=
  (biprod.mapIso (eqToIso (leftSumObj_kernel_eq T E))
    (eqToIso (leftSumObj_kernel_eq U F))).inv ≫
      convolutionKernel (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)

@[reassoc]
private theorem actionCanonicalKernel_first (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionCanonicalKernel T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).fst ≫
      (eqToIso (leftSumObj_middle_eq T E)).hom =
    (biprod.fst : (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A) ⟶ T.of ⊞ E.A) ≫
      biprod.map (𝟙 T.of) E.i := by
  simp only [actionCanonicalKernel, Category.assoc, convolutionKernel_fst_assoc,
    biprod.mapIso, biprod.map_fst_assoc]
  have hi : (eqToIso (leftSumObj_kernel_eq T E)).inv ≫
      (FixedTargetExtension.leftSumObj T E).i ≫
      (eqToIso (leftSumObj_middle_eq T E)).hom = biprod.map (𝟙 T.of) E.i := by
    rw [← Category.assoc, leftSumObj_i_pre_kernel]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg
    (fun f : T.of ⊞ E.A ⟶ T.of ⊞ E.B =>
      (biprod.fst : (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A) ⟶ T.of ⊞ E.A) ≫ f) hi

@[reassoc]
private theorem actionCanonicalKernel_second (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionCanonicalKernel T U E F ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F)).snd ≫
      (eqToIso (leftSumObj_middle_eq U F)).hom =
    (biprod.snd : (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A) ⟶ U.of ⊞ F.A) ≫
      biprod.map (𝟙 U.of) F.i := by
  simp only [actionCanonicalKernel, Category.assoc, convolutionKernel_snd_assoc,
    biprod.mapIso, biprod.map_snd_assoc]
  have hi : (eqToIso (leftSumObj_kernel_eq U F)).inv ≫
      (FixedTargetExtension.leftSumObj U F).i ≫
      (eqToIso (leftSumObj_middle_eq U F)).hom = biprod.map (𝟙 U.of) F.i := by
    rw [← Category.assoc, leftSumObj_i_pre_kernel]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg
    (fun f : U.of ⊞ F.A ⟶ U.of ⊞ F.B =>
      (biprod.snd : (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A) ⟶ U.of ⊞ F.A) ≫ f) hi

private theorem actionConvolution_kernel_canonical (T U : Core C)
    (E F : FixedTargetExtension C X) :
    biprod.map (𝟙 (T.of ⊞ U.of)) (convolutionKernel E F) ≫
      actionConvolutionMiddle T U E F =
    (exchangeIso T.of U.of E.A F.A).hom ≫ actionCanonicalKernel T U E F := by
  apply (convolutionPullback (FixedTargetExtension.leftSumObj T E)
    (FixedTargetExtension.leftSumObj U F)).square.hom_ext
  · apply (cancel_mono (eqToIso (leftSumObj_middle_eq T E)).hom).mp
    simp only [Category.assoc, actionConvolutionMiddle_first_native,
      actionCanonicalKernel_first]
    apply biprod.hom_ext
    · simp [actionConvolutionFirst, exchangeIso, Category.assoc]
    · simp [actionConvolutionFirst, exchangeIso, Category.assoc,
        convolutionKernel_fst]
  · apply (cancel_mono (eqToIso (leftSumObj_middle_eq U F)).hom).mp
    simp only [Category.assoc, actionConvolutionMiddle_second_native,
      actionCanonicalKernel_second]
    apply biprod.hom_ext
    · simp [actionConvolutionSecond, exchangeIso, Category.assoc]
    · simp [actionConvolutionSecond, exchangeIso, Category.assoc,
        convolutionKernel_snd]

/-- The stabilization comparison preserves the two actual kernel inclusions. -/
theorem actionConvolution_kernel_square (T U : Core C) (E F : FixedTargetExtension C X) :
    (FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).i ≫
        actionConvolutionMiddle T U E F =
      (exchangeIso T.of U.of E.A F.A).hom ≫
        (convolutionObj (FixedTargetExtension.leftSumObj T E)
          (FixedTargetExtension.leftSumObj U F)).i := by
  let S := FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)
  let E1 := FixedTargetExtension.leftSumObj T E
  let F1 := FixedTargetExtension.leftSumObj U F
  let Q := convolutionObj E1 F1
  let P := convolutionPullback E1 F1
  let M := (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj
  let A := (T.of ⊞ U.of) ⊞ (E.A ⊞ F.A)
  let B := (T.of ⊞ E.A) ⊞ (U.of ⊞ F.A)
  let iS : S.A ⟶ S.B := S.i
  let iQ : Q.A ⟶ Q.B := Q.i
  let m : S.B ⟶ Q.B := actionConvolutionMiddle T U E F
  let x : S.A ⟶ Q.A := (exchangeIso T.of U.of E.A F.A).hom
  let mc : M ⟶ P.obj := actionConvolutionMiddle T U E F
  let xc : A ⟶ B := (exchangeIso T.of U.of E.A F.A).hom
  have hm : HEq m mc := by rfl
  have hx : HEq x xc := by rfl
  have hiS : HEq iS
      (biprod.map (𝟙 (T.of ⊞ U.of)) (convolutionKernel E F)) :=
    actionTensor_i_heq T U E F
  have hiQ : HEq (actionCanonicalKernel T U E F) iQ := by
    have hB : HEq (actionCanonicalKernel T U E F) (convolutionKernel E1 F1) :=
      actionBiprodEqIso_inv_comp_heq (leftSumObj_kernel_eq T E)
        (leftSumObj_kernel_eq U F) (convolutionKernel E1 F1)
    exact hB.trans (convolutionObj_i_heq E1 F1).symm
  have hL := heq_comp (actionTensor_kernel_eq T U E F)
    (leftSumTensor_middle_eq T U E F) (convolutionObj_middle_eq E1 F1) hiS hm
  have hB : Q.A = B :=
    (convolutionObj_kernel_eq E1 F1).trans
      (congrArg₂ (fun Y Z : C => Y ⊞ Z)
        (leftSumObj_kernel_eq T E) (leftSumObj_kernel_eq U F))
  have hR := heq_comp (actionTensor_kernel_eq T U E F) hB
    (convolutionObj_middle_eq E1 F1) hx hiQ.symm
  exact eq_of_heq (hL.trans
    ((heq_of_eq (actionConvolution_kernel_canonical T U E F)).trans hR.symm))

private theorem actionConvolution_quotient_canonical (T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
      convolutionQuotient (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F) =
      (biprod.snd : (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj ⟶
        (convolutionPullback E F).obj) ≫ convolutionQuotient E F := by
  let E1 := FixedTargetExtension.leftSumObj T E
  let F1 := FixedTargetExtension.leftSumObj U F
  let P := convolutionPullback E1 F1
  have hE := congrArg
    (fun q : E1.B ⟶ X => (actionConvolutionMiddle T U E F ≫ P.fst) ≫ q)
    (leftSumObj_middleIso_hom_p T E)
  have hNative :
      (actionConvolutionMiddle T U E F ≫ P.fst) ≫
        ((eqToIso (leftSumObj_middle_eq T E)).hom ≫ biprod.snd ≫ E.p) =
      biprod.snd ≫ ((convolutionPullback E F).fst ≫ E.p) := by
    have hFirst := congrArg
      (fun q : ((T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj) ⟶ (T.of ⊞ E.B) =>
        q ≫ biprod.snd ≫ E.p)
      (actionConvolutionMiddle_first_native T U E F)
    simpa only [P, E1, F1, Category.assoc, actionConvolutionFirst,
      biprod.lift_snd_assoc] using hFirst
  change actionConvolutionMiddle T U E F ≫ (P.fst ≫ E1.p) =
    biprod.snd ≫ ((convolutionPullback E F).fst ≫ E.p)
  exact (Category.assoc (actionConvolutionMiddle T U E F) P.fst E1.p).symm.trans
    (hE.symm.trans hNative)

/-- The quotient square retains the original source and target row maps. -/
theorem actionConvolution_quotient_square (T U : Core C) (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T U E F ≫
        (convolutionObj (FixedTargetExtension.leftSumObj T E)
          (FixedTargetExtension.leftSumObj U F)).p =
      (FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)).p := by
  let S := FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F)
  let E1 := FixedTargetExtension.leftSumObj T E
  let F1 := FixedTargetExtension.leftSumObj U F
  let Q := convolutionObj E1 F1
  let P := convolutionPullback E1 F1
  let M := (T.of ⊞ U.of) ⊞ (convolutionPullback E F).obj
  let m : S.B ⟶ Q.B := actionConvolutionMiddle T U E F
  let mc : M ⟶ P.obj := actionConvolutionMiddle T U E F
  have hm : HEq m mc := by rfl
  have hp : HEq Q.p (convolutionQuotient E1 F1) := convolutionObj_p_heq E1 F1
  have hL := heq_comp (leftSumTensor_middle_eq T U E F)
    (convolutionObj_middle_eq E1 F1) (rfl : X = X) hm hp
  have hR := actionTensor_p_heq T U E F
  exact eq_of_heq (hL.trans
    ((heq_of_eq (actionConvolution_quotient_canonical T U E F)).trans hR.symm))

/-- The actual comparison keeps both original stabilizing summands. -/
def actionConvolutionIso (T U : Core C) (E F : FixedTargetExtension C X) :
    FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F) ≅
      convolutionObj (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F) := by
  let h : FixedTargetExtension.leftSumObj (T ⊗ U) (convolutionObj E F) ⟶
      convolutionObj (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F) :=
    { a := exchangeIso T.of U.of E.A F.A
      b := actionConvolutionMiddleIso T U E F
      comm_i := by exact actionConvolution_kernel_square T U E F
      comm_p := by exact actionConvolution_quotient_square T U E F }
  exact FixedTargetExtension.pairIso h

@[simp]
theorem actionConvolutionIso_middle (T U : Core C) (E F : FixedTargetExtension C X) :
    (actionConvolutionIso T U E F).hom.b.hom = actionConvolutionMiddle T U E F := rfl

omit [HasZeroObject C] [ExactCategory C] in
private theorem biprod_map_heq {A A' B B' D D' Z Z' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hZ : Z = Z')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ Z} {g' : D' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (biprod.map f g) (biprod.map f' g') := by
  cases hA
  cases hB
  cases hD
  cases hZ
  cases hf
  cases hg
  rfl

private theorem actionConvolution_natural_canonical {T T' U U' : Core C}
    (t : T ⟶ T') (u : U ⟶ U') {E E' F F' : FixedTargetExtension C X}
    (f : E ⟶ E') (g : F ⟶ F') :
    biprod.map (biprod.map t.iso.hom u.iso.hom) (convolutionMiddleMap f g) ≫
      actionConvolutionMiddle T' U' E' F' =
    actionConvolutionMiddle T U E F ≫
      convolutionMiddleMap (FixedTargetExtension.leftSumMap t f)
        (FixedTargetExtension.leftSumMap u g) := by
  apply (convolutionPullback (FixedTargetExtension.leftSumObj T' E')
    (FixedTargetExtension.leftSumObj U' F')).square.hom_ext
  · apply (cancel_mono (eqToIso (leftSumObj_middle_eq T' E')).hom).mp
    simp only [Category.assoc, convolutionMiddleMap_fst_assoc,
      leftSumMap_middle_post,
      actionConvolutionMiddle_first_native, actionConvolutionMiddle_first_native_assoc]
    apply biprod.hom_ext <;>
      simp [Category.assoc, actionConvolutionFirst, convolutionMiddleMap_fst]
  · apply (cancel_mono (eqToIso (leftSumObj_middle_eq U' F')).hom).mp
    simp only [Category.assoc, convolutionMiddleMap_snd_assoc,
      leftSumMap_middle_post,
      actionConvolutionMiddle_second_native, actionConvolutionMiddle_second_native_assoc]
    apply biprod.hom_ext <;>
      simp [Category.assoc, actionConvolutionSecond, convolutionMiddleMap_snd]

/-- Naturality retains both stabilizer maps and both original row maps. -/
theorem actionConvolutionIso_natural {T T' U U' : Core C} (t : T ⟶ T') (u : U ⟶ U')
    {E E' F F' : FixedTargetExtension C X} (f : E ⟶ E') (g : F ⟶ F') :
    FixedTargetExtension.leftSumMap (t ⊗ₘ u) (convolutionMap f g) ≫
        (actionConvolutionIso T' U' E' F').hom =
      (actionConvolutionIso T U E F).hom ≫ convolutionMap
        (FixedTargetExtension.leftSumMap t f) (FixedTargetExtension.leftSumMap u g) := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  let l := FixedTargetExtension.leftSumMap (t ⊗ₘ u) (convolutionMap f g) ≫
    (actionConvolutionIso T' U' E' F').hom
  let r := (actionConvolutionIso T U E F).hom ≫ convolutionMap
    (FixedTargetExtension.leftSumMap t f) (FixedTargetExtension.leftSumMap u g)
  let lc := biprod.map (biprod.map t.iso.hom u.iso.hom) (convolutionMiddleMap f g) ≫
    actionConvolutionMiddle T' U' E' F'
  let rc := actionConvolutionMiddle T U E F ≫
    convolutionMiddleMap (FixedTargetExtension.leftSumMap t f)
      (FixedTargetExtension.leftSumMap u g)
  have hl : HEq l.b.hom lc := by
    have hT : (T ⊗ U).of = (T.of ⊞ U.of) := rfl
    have hT' : (T' ⊗ U').of = (T'.of ⊞ U'.of) := rfl
    have hMap := biprod_map_heq hT hT'
      (convolutionObj_middle_eq E F) (convolutionObj_middle_eq E' F')
      (heq_of_eq (coreBiprodTensorHom_iso_hom t u))
      (heq_of_eq (convolutionMap_middle f g))
    have hField := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
      (t ⊗ₘ u) (convolutionMap f g))).trans hMap
    have hComp := heq_comp (leftSumTensor_middle_eq T U E F)
      (leftSumTensor_middle_eq T' U' E' F')
      (convolutionObj_middle_eq (FixedTargetExtension.leftSumObj T' E')
        (FixedTargetExtension.leftSumObj U' F'))
      hField (heq_of_eq (actionConvolutionIso_middle T' U' E' F'))
    have hRow := congrArg Iso.hom (FixedTargetExtension.comp_b
      (FixedTargetExtension.leftSumMap (t ⊗ₘ u) (convolutionMap f g))
      (actionConvolutionIso T' U' E' F').hom)
    exact (heq_of_eq hRow).trans hComp
  have hr : HEq r.b.hom rc := by
    have hComp := heq_comp (leftSumTensor_middle_eq T U E F)
      (convolutionObj_middle_eq (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F))
      (convolutionObj_middle_eq (FixedTargetExtension.leftSumObj T' E')
        (FixedTargetExtension.leftSumObj U' F'))
      (heq_of_eq (actionConvolutionIso_middle T U E F))
      (heq_of_eq (convolutionMap_middle (FixedTargetExtension.leftSumMap t f)
        (FixedTargetExtension.leftSumMap u g)))
    have hRow := congrArg Iso.hom (FixedTargetExtension.comp_b
      (actionConvolutionIso T U E F).hom
      (convolutionMap (FixedTargetExtension.leftSumMap t f)
        (FixedTargetExtension.leftSumMap u g)))
    exact (heq_of_eq hRow).trans hComp
  exact eq_of_heq (hl.trans ((heq_of_eq
    (actionConvolution_natural_canonical t u f g)).trans hr.symm))

end AlgebraicKTheory.AuxiliaryExtension

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction


/-- The actual exchange of the two later/earlier stabilizer pairs. -/
def stabilizerExchange (T U V W : Core C) :
    (T ⊗ U) ⊗ (V ⊗ W) ≅ (T ⊗ V) ⊗ (U ⊗ W) :=
  Core.isoMk (exchangeIso T.of U.of V.of W.of)

omit [ExactCategory C] in
@[simp]
theorem stabilizerExchange_hom (T U V W : Core C) :
    (stabilizerExchange T U V W).hom.iso.hom = (exchangeIso T.of U.of V.of W.of).hom := rfl

/-- The action comparison is compatible with the two actual action associators. -/
private theorem nestedLeftSum_middle_eq (T U : Core C) (E : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj T (FixedTargetExtension.leftSumObj U E)).B) =
      (T.of ⊞ (U.of ⊞ E.B)) :=
  (leftSumObj_middle_eq T (FixedTargetExtension.leftSumObj U E)).trans
    (congrArg (fun Y : C => T.of ⊞ Y) (leftSumObj_middle_eq U E))

private def nestedLeftSumMiddleIso (T U : Core C) (E : FixedTargetExtension C X) :
    (FixedTargetExtension.leftSumObj T (FixedTargetExtension.leftSumObj U E)).B ≅
      T.of ⊞ (U.of ⊞ E.B) :=
  eqToIso (leftSumObj_middle_eq T (FixedTargetExtension.leftSumObj U E)) ≪≫
    biprod.mapIso (Iso.refl T.of) (eqToIso (leftSumObj_middle_eq U E))

omit [HasZeroObject C] [ExactCategory C] in
private theorem biprodRightEqIso_eq (T : C) {A B : C} (p : A = B) :
    biprod.mapIso (Iso.refl T) (eqToIso p) =
      eqToIso (congrArg (fun Y : C => T ⊞ Y) p) := by
  cases p
  apply Iso.ext
  apply biprod.hom_ext <;> simp [biprod.mapIso]

private theorem nestedLeftSumMiddleIso_eq (T U : Core C) (E : FixedTargetExtension C X) :
    nestedLeftSumMiddleIso T U E = eqToIso (nestedLeftSum_middle_eq T U E) := by
  unfold nestedLeftSumMiddleIso
  rw [biprodRightEqIso_eq, eqToIso_trans]

@[reassoc]
private theorem leftSumAssoc_middle_native (T U : Core C) (E : FixedTargetExtension C X) :
    (eqToIso (leftSumObj_middle_eq (T ⊗ U) E)).inv ≫
      (FixedTargetExtension.leftSumAssocIso T U E).hom.b.hom ≫
        (nestedLeftSumMiddleIso T U E).hom = (biprod.associator T.of U.of E.B).hom := by
  have h := (conj_eqToHom_iff_heq (FixedTargetExtension.leftSumAssocIso T U E).hom.b.hom
    (biprod.associator T.of U.of E.B).hom
    (leftSumObj_middle_eq (T ⊗ U) E) (nestedLeftSum_middle_eq T U E)).2
      (heq_of_eq (FixedTargetExtension.leftSumAssocIso_b_hom T U E))
  have hh : (FixedTargetExtension.leftSumAssocIso T U E).hom.b.hom =
      (eqToIso (leftSumObj_middle_eq (T ⊗ U) E)).hom ≫
        (biprod.associator T.of U.of E.B).hom ≫
          (eqToIso (nestedLeftSum_middle_eq T U E)).inv := by
    simpa only [eqToIso.hom, eqToIso.inv] using h
  rw [nestedLeftSumMiddleIso_eq, hh]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
private theorem actionConvolution_first_nested (T' U' T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T' U' (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F) ≫
      (convolutionPullback
        (FixedTargetExtension.leftSumObj T' (FixedTargetExtension.leftSumObj T E))
        (FixedTargetExtension.leftSumObj U' (FixedTargetExtension.leftSumObj U F))).fst ≫
      (nestedLeftSumMiddleIso T' T E).hom =
    actionConvolutionFirst T' U' (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F) ≫
        biprod.map (𝟙 T'.of) (eqToIso (leftSumObj_middle_eq T E)).hom := by
  simp only [nestedLeftSumMiddleIso, Iso.trans_hom, biprod.mapIso,
    actionConvolutionMiddle_first_assoc, Iso.inv_hom_id_assoc,
    Iso.refl_hom]

@[reassoc]
private theorem actionConvolution_second_nested (T' U' T U : Core C)
    (E F : FixedTargetExtension C X) :
    actionConvolutionMiddle T' U' (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F) ≫
      (convolutionPullback
        (FixedTargetExtension.leftSumObj T' (FixedTargetExtension.leftSumObj T E))
        (FixedTargetExtension.leftSumObj U' (FixedTargetExtension.leftSumObj U F))).snd ≫
      (nestedLeftSumMiddleIso U' U F).hom =
    actionConvolutionSecond T' U' (FixedTargetExtension.leftSumObj T E)
      (FixedTargetExtension.leftSumObj U F) ≫
        biprod.map (𝟙 U'.of) (eqToIso (leftSumObj_middle_eq U F)).hom := by
  simp only [nestedLeftSumMiddleIso, Iso.trans_hom, biprod.mapIso,
    actionConvolutionMiddle_second_assoc, Iso.inv_hom_id_assoc,
    Iso.refl_hom]

omit [HasZeroObject C] [ExactCategory C] in
private theorem biprod_assoc_hom_heq {A A' B B' D D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') :
    HEq (biprod.associator A B D).hom (biprod.associator A' B' D').hom := by
  cases hA
  cases hB
  cases hD
  rfl

private theorem actionConvolution_assoc_canonical (T' U' T U : Core C)
    (E F : FixedTargetExtension C X) :
    biprod.map (exchangeIso T'.of U'.of T.of U.of).hom
        (𝟙 (convolutionPullback E F).obj) ≫
      actionConvolutionMiddle (T' ⊗ T) (U' ⊗ U) E F ≫
      convolutionMiddleMap (FixedTargetExtension.leftSumAssocIso T' T E).hom
        (FixedTargetExtension.leftSumAssocIso U' U F).hom =
    (biprod.associator (T'.of ⊞ U'.of) (T.of ⊞ U.of)
      (convolutionPullback E F).obj).hom ≫
      biprod.map (𝟙 (T'.of ⊞ U'.of)) (actionConvolutionMiddle T U E F) ≫
      actionConvolutionMiddle T' U' (FixedTargetExtension.leftSumObj T E)
        (FixedTargetExtension.leftSumObj U F) := by
  let P := convolutionPullback E F
  let E1 := FixedTargetExtension.leftSumObj T E
  let F1 := FixedTargetExtension.leftSumObj U F
  let Q := convolutionPullback E1 F1
  let Z := convolutionPullback (FixedTargetExtension.leftSumObj T' E1)
    (FixedTargetExtension.leftSumObj U' F1)
  let W := ((T'.of ⊞ U'.of) ⊞ (T.of ⊞ U.of)) ⊞ P.obj
  let l₀ : W ⟶ ((T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)) ⊞ P.obj :=
    biprod.map (exchangeIso T'.of U'.of T.of U.of).hom (𝟙 P.obj)
  let l₁ := actionConvolutionMiddle (T' ⊗ T) (U' ⊗ U) E F
  let l₂ := convolutionMiddleMap (FixedTargetExtension.leftSumAssocIso T' T E).hom
    (FixedTargetExtension.leftSumAssocIso U' U F).hom
  let r₀ : W ⟶ (T'.of ⊞ U'.of) ⊞ ((T.of ⊞ U.of) ⊞ P.obj) :=
    (biprod.associator (T'.of ⊞ U'.of) (T.of ⊞ U.of) P.obj).hom
  let r₁ : (T'.of ⊞ U'.of) ⊞ ((T.of ⊞ U.of) ⊞ P.obj) ⟶
      (T'.of ⊞ U'.of) ⊞ Q.obj :=
    biprod.map (𝟙 (T'.of ⊞ U'.of)) (actionConvolutionMiddle T U E F)
  let r₂ := actionConvolutionMiddle T' U' E1 F1
  let eE := nestedLeftSumMiddleIso T' T E
  let eF := nestedLeftSumMiddleIso U' U F
  have hLeftE : l₁ ≫ l₂ ≫ Z.fst ≫ eE.hom =
      actionConvolutionFirst (T' ⊗ T) (U' ⊗ U) E F ≫
        (biprod.associator T'.of T.of E.B).hom := by
    simp only [l₁, l₂, Z, E1, F1, eE,
      convolutionMiddleMap_fst_assoc, actionConvolutionMiddle_first_assoc,
      leftSumAssoc_middle_native]
  have hLeftF : l₁ ≫ l₂ ≫ Z.snd ≫ eF.hom =
      actionConvolutionSecond (T' ⊗ T) (U' ⊗ U) E F ≫
        (biprod.associator U'.of U.of F.B).hom := by
    simp only [l₁, l₂, Z, E1, F1, eF,
      convolutionMiddleMap_snd_assoc, actionConvolutionMiddle_second_assoc,
      leftSumAssoc_middle_native]
  have hRightE : r₂ ≫ Z.fst ≫ eE.hom =
      actionConvolutionFirst T' U' E1 F1 ≫
        biprod.map (𝟙 T'.of) (eqToIso (leftSumObj_middle_eq T E)).hom :=
    actionConvolution_first_nested T' U' T U E F
  have hRightF : r₂ ≫ Z.snd ≫ eF.hom =
      actionConvolutionSecond T' U' E1 F1 ≫
        biprod.map (𝟙 U'.of) (eqToIso (leftSumObj_middle_eq U F)).hom :=
    actionConvolution_second_nested T' U' T U E F
  -- All projections below are bound at their actual C-arrow types.
  let K₀ : C := T'.of ⊞ U'.of
  let K₁ : C := T.of ⊞ U.of
  let S : C := K₀ ⊞ K₁
  let V : C := (T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)
  let D₀ : C := K₁ ⊞ P.obj
  let κ : W ⟶ S := biprod.fst
  let π : W ⟶ P.obj := biprod.snd
  let s₀ : S ⟶ K₀ := biprod.fst
  let s₁ : S ⟶ K₁ := biprod.snd
  let k₀ : K₀ ⟶ T'.of := biprod.fst
  let k₀' : K₀ ⟶ U'.of := biprod.snd
  let k₁ : K₁ ⟶ T.of := biprod.fst
  let k₁' : K₁ ⟶ U.of := biprod.snd
  let v₀ : V ⟶ T'.of ⊞ T.of := biprod.fst
  let v₁ : V ⟶ U'.of ⊞ U.of := biprod.snd
  let a₀ : T'.of ⊞ T.of ⟶ T'.of := biprod.fst
  let a₁ : T'.of ⊞ T.of ⟶ T.of := biprod.snd
  let b₀ : U'.of ⊞ U.of ⟶ U'.of := biprod.fst
  let b₁ : U'.of ⊞ U.of ⟶ U.of := biprod.snd
  let vFst : V ⊞ P.obj ⟶ V := biprod.fst
  let vSnd : V ⊞ P.obj ⟶ P.obj := biprod.snd
  let dFst : D₀ ⟶ K₁ := biprod.fst
  let dSnd : D₀ ⟶ P.obj := biprod.snd
  let rFst : K₀ ⊞ D₀ ⟶ K₀ := biprod.fst
  let rSnd : K₀ ⊞ D₀ ⟶ D₀ := biprod.snd
  let qFst : K₀ ⊞ Q.obj ⟶ K₀ := biprod.fst
  let qSnd : K₀ ⊞ Q.obj ⟶ Q.obj := biprod.snd
  let σ : S ⟶ V := (exchangeIso T'.of U'.of T.of U.of).hom
  let m : D₀ ⟶ Q.obj := actionConvolutionMiddle T U E F
  let cE : E1.B ⟶ T.of ⊞ E.B := (eqToIso (leftSumObj_middle_eq T E)).hom
  let cF : F1.B ⟶ U.of ⊞ F.B := (eqToIso (leftSumObj_middle_eq U F)).hom
  let LE : V ⊞ P.obj ⟶ (T'.of ⊞ T.of) ⊞ E.B :=
    actionConvolutionFirst (T' ⊗ T) (U' ⊗ U) E F
  let LF : V ⊞ P.obj ⟶ (U'.of ⊞ U.of) ⊞ F.B :=
    actionConvolutionSecond (T' ⊗ T) (U' ⊗ U) E F
  let IE : D₀ ⟶ T.of ⊞ E.B := actionConvolutionFirst T U E F
  let IF : D₀ ⟶ U.of ⊞ F.B := actionConvolutionSecond T U E F
  let OE : K₀ ⊞ Q.obj ⟶ T'.of ⊞ E1.B := actionConvolutionFirst T' U' E1 F1
  let OF : K₀ ⊞ Q.obj ⟶ U'.of ⊞ F1.B := actionConvolutionSecond T' U' E1 F1
  let ME : T'.of ⊞ E1.B ⟶ T'.of ⊞ (T.of ⊞ E.B) := biprod.map (𝟙 T'.of) cE
  let MF : U'.of ⊞ F1.B ⟶ U'.of ⊞ (U.of ⊞ F.B) := biprod.map (𝟙 U'.of) cF
  let AE : (T'.of ⊞ T.of) ⊞ E.B ⟶ T'.of ⊞ (T.of ⊞ E.B) :=
    (biprod.associator T'.of T.of E.B).hom
  let AF : (U'.of ⊞ U.of) ⊞ F.B ⟶ U'.of ⊞ (U.of ⊞ F.B) :=
    (biprod.associator U'.of U.of F.B).hom
  let leFst : (T'.of ⊞ T.of) ⊞ E.B ⟶ T'.of ⊞ T.of := biprod.fst
  let leSnd : (T'.of ⊞ T.of) ⊞ E.B ⟶ E.B := biprod.snd
  let lfFst : (U'.of ⊞ U.of) ⊞ F.B ⟶ U'.of ⊞ U.of := biprod.fst
  let lfSnd : (U'.of ⊞ U.of) ⊞ F.B ⟶ F.B := biprod.snd
  let ieFst : T.of ⊞ E.B ⟶ T.of := biprod.fst
  let ieSnd : T.of ⊞ E.B ⟶ E.B := biprod.snd
  let ifFst : U.of ⊞ F.B ⟶ U.of := biprod.fst
  let ifSnd : U.of ⊞ F.B ⟶ F.B := biprod.snd
  let oeFst : T'.of ⊞ E1.B ⟶ T'.of := biprod.fst
  let oeSnd : T'.of ⊞ E1.B ⟶ E1.B := biprod.snd
  let ofFst : U'.of ⊞ F1.B ⟶ U'.of := biprod.fst
  let ofSnd : U'.of ⊞ F1.B ⟶ F1.B := biprod.snd
  let eFst : T'.of ⊞ (T.of ⊞ E.B) ⟶ T'.of := biprod.fst
  let eSnd : T'.of ⊞ (T.of ⊞ E.B) ⟶ T.of ⊞ E.B := biprod.snd
  let fFst : U'.of ⊞ (U.of ⊞ F.B) ⟶ U'.of := biprod.fst
  let fSnd : U'.of ⊞ (U.of ⊞ F.B) ⟶ U.of ⊞ F.B := biprod.snd
  let leftE : W ⟶ T'.of ⊞ (T.of ⊞ E.B) := l₀ ≫ LE ≫ AE
  let rightE : W ⟶ T'.of ⊞ (T.of ⊞ E.B) := r₀ ≫ r₁ ≫ OE ≫ ME
  let leftF : W ⟶ U'.of ⊞ (U.of ⊞ F.B) := l₀ ≫ LF ≫ AF
  let rightF : W ⟶ U'.of ⊞ (U.of ⊞ F.B) := r₀ ≫ r₁ ≫ OF ≫ MF
  -- Three native associator characteristics, derived from the actual lifts.
  have assoc₀ (A B D : C) :
      (biprod.associator A B D).hom ≫ (biprod.fst : A ⊞ (B ⊞ D) ⟶ A) =
        (biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A) := by
    exact biprod.lift_fst ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A))
      (biprod.lift ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) (biprod.snd :
          (A ⊞ B) ⊞ D ⟶ D))
  have assoc₁ (A B D : C) :
      (biprod.associator A B D).hom ≫ (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) ≫
        (biprod.fst : B ⊞ D ⟶ B) = (biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)
            := by
    have h : (biprod.associator A B D).hom ≫ (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) =
        biprod.lift ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) (biprod.snd
            : (A ⊞ B) ⊞ D ⟶ D) := by
      exact biprod.lift_snd ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A))
        (biprod.lift ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) (biprod.snd
            : (A ⊞ B) ⊞ D ⟶ D))
    exact (Category.assoc (biprod.associator A B D).hom
      (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) (biprod.fst : B ⊞ D ⟶ B)).symm.trans
      ((congrArg (fun q : (A ⊞ B) ⊞ D ⟶ B ⊞ D => q ≫ (biprod.fst : B ⊞ D ⟶ B)) h).trans
        (biprod.lift_fst ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B))
            (biprod.snd : (A ⊞ B) ⊞ D ⟶ D)))
  have assoc₂ (A B D : C) :
      (biprod.associator A B D).hom ≫ (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) ≫
        (biprod.snd : B ⊞ D ⟶ D) = (biprod.snd : (A ⊞ B) ⊞ D ⟶ D) := by
    have h : (biprod.associator A B D).hom ≫ (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) =
        biprod.lift ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) (biprod.snd
            : (A ⊞ B) ⊞ D ⟶ D) := by
      exact biprod.lift_snd ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A))
        (biprod.lift ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) (biprod.snd
            : (A ⊞ B) ⊞ D ⟶ D))
    exact (Category.assoc (biprod.associator A B D).hom
      (biprod.snd : A ⊞ (B ⊞ D) ⟶ B ⊞ D) (biprod.snd : B ⊞ D ⟶ D)).symm.trans
      ((congrArg (fun q : (A ⊞ B) ⊞ D ⟶ B ⊞ D => q ≫ (biprod.snd : B ⊞ D ⟶ D)) h).trans
        (biprod.lift_snd ((biprod.fst : (A ⊞ B) ⊞ D ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B))
            (biprod.snd : (A ⊞ B) ⊞ D ⟶ D)))
  have hl₀fst : l₀ ≫ vFst = κ ≫ σ := by
    exact biprod.map_fst σ (𝟙 P.obj)
  have hl₀snd : l₀ ≫ vSnd = π := by
    exact (biprod.map_snd σ (𝟙 P.obj)).trans (Category.comp_id π)
  have hr₁fst : r₁ ≫ qFst = rFst := by
    exact (biprod.map_fst (𝟙 K₀) m).trans (Category.comp_id rFst)
  have hr₁snd : r₁ ≫ qSnd = rSnd ≫ m := by
    exact biprod.map_snd (𝟙 K₀) m
  have hr₀fst : r₀ ≫ rFst = κ ≫ s₀ := by
    exact assoc₀ K₀ K₁ P.obj
  have hr₀ker : r₀ ≫ rSnd ≫ dFst = κ ≫ s₁ := by
    exact assoc₁ K₀ K₁ P.obj
  have hr₀pb : r₀ ≫ rSnd ≫ dSnd = π := by
    exact assoc₂ K₀ K₁ P.obj
  have hσfst : σ ≫ v₀ = biprod.lift (s₀ ≫ k₀) (s₁ ≫ k₁) := by
    exact biprod.lift_fst (biprod.lift (s₀ ≫ k₀) (s₁ ≫ k₁))
      (biprod.lift (s₀ ≫ k₀') (s₁ ≫ k₁'))
  have hσsnd : σ ≫ v₁ = biprod.lift (s₀ ≫ k₀') (s₁ ≫ k₁') := by
    exact biprod.lift_snd (biprod.lift (s₀ ≫ k₀) (s₁ ≫ k₁))
      (biprod.lift (s₀ ≫ k₀') (s₁ ≫ k₁'))
  have hσA : σ ≫ v₀ ≫ a₀ = s₀ ≫ k₀ := by
    exact (Category.assoc σ v₀ a₀).symm.trans
      ((congrArg (fun q : S ⟶ T'.of ⊞ T.of => q ≫ a₀) hσfst).trans
        (biprod.lift_fst (s₀ ≫ k₀) (s₁ ≫ k₁)))
  have hσT : σ ≫ v₀ ≫ a₁ = s₁ ≫ k₁ := by
    exact (Category.assoc σ v₀ a₁).symm.trans
      ((congrArg (fun q : S ⟶ T'.of ⊞ T.of => q ≫ a₁) hσfst).trans
        (biprod.lift_snd (s₀ ≫ k₀) (s₁ ≫ k₁)))
  have hσB : σ ≫ v₁ ≫ b₀ = s₀ ≫ k₀' := by
    exact (Category.assoc σ v₁ b₀).symm.trans
      ((congrArg (fun q : S ⟶ U'.of ⊞ U.of => q ≫ b₀) hσsnd).trans
        (biprod.lift_fst (s₀ ≫ k₀') (s₁ ≫ k₁')))
  have hσU : σ ≫ v₁ ≫ b₁ = s₁ ≫ k₁' := by
    exact (Category.assoc σ v₁ b₁).symm.trans
      ((congrArg (fun q : S ⟶ U'.of ⊞ U.of => q ≫ b₁) hσsnd).trans
        (biprod.lift_snd (s₀ ≫ k₀') (s₁ ≫ k₁')))
  have hLEfst : LE ≫ leFst = vFst ≫ v₀ := by
    exact biprod.lift_fst (vFst ≫ v₀) (vSnd ≫ P.fst)
  have hLEsnd : LE ≫ leSnd = vSnd ≫ P.fst := by
    exact biprod.lift_snd (vFst ≫ v₀) (vSnd ≫ P.fst)
  have hLFfst : LF ≫ lfFst = vFst ≫ v₁ := by
    exact biprod.lift_fst (vFst ≫ v₁) (vSnd ≫ P.snd)
  have hLFsnd : LF ≫ lfSnd = vSnd ≫ P.snd := by
    exact biprod.lift_snd (vFst ≫ v₁) (vSnd ≫ P.snd)
  have hIEfst : IE ≫ ieFst = dFst ≫ k₁ := by
    exact biprod.lift_fst (dFst ≫ k₁) (dSnd ≫ P.fst)
  have hIEsnd : IE ≫ ieSnd = dSnd ≫ P.fst := by
    exact biprod.lift_snd (dFst ≫ k₁) (dSnd ≫ P.fst)
  have hIFfst : IF ≫ ifFst = dFst ≫ k₁' := by
    exact biprod.lift_fst (dFst ≫ k₁') (dSnd ≫ P.snd)
  have hIFsnd : IF ≫ ifSnd = dSnd ≫ P.snd := by
    exact biprod.lift_snd (dFst ≫ k₁') (dSnd ≫ P.snd)
  have hOEfst : OE ≫ oeFst = qFst ≫ k₀ := by
    exact biprod.lift_fst (qFst ≫ k₀) (qSnd ≫ Q.fst)
  have hOEsnd : OE ≫ oeSnd = qSnd ≫ Q.fst := by
    exact biprod.lift_snd (qFst ≫ k₀) (qSnd ≫ Q.fst)
  have hOFfst : OF ≫ ofFst = qFst ≫ k₀' := by
    exact biprod.lift_fst (qFst ≫ k₀') (qSnd ≫ Q.snd)
  have hOFsnd : OF ≫ ofSnd = qSnd ≫ Q.snd := by
    exact biprod.lift_snd (qFst ≫ k₀') (qSnd ≫ Q.snd)
  have hMEfst : ME ≫ eFst = oeFst := by
    exact (biprod.map_fst (𝟙 T'.of) cE).trans (Category.comp_id oeFst)
  have hMEsnd : ME ≫ eSnd = oeSnd ≫ cE := by
    exact biprod.map_snd (𝟙 T'.of) cE
  have hMFfst : MF ≫ fFst = ofFst := by
    exact (biprod.map_fst (𝟙 U'.of) cF).trans (Category.comp_id ofFst)
  have hMFsnd : MF ≫ fSnd = ofSnd ≫ cF := by
    exact biprod.map_snd (𝟙 U'.of) cF
  have hInnerE : m ≫ Q.fst ≫ cE = IE := by
    exact actionConvolutionMiddle_first_native T U E F
  have hInnerF : m ≫ Q.snd ≫ cF = IF := by
    exact actionConvolutionMiddle_second_native T U E F
  have hAE₀ : AE ≫ eFst = leFst ≫ a₀ := by
    exact assoc₀ T'.of T.of E.B
  have hAE₁ : AE ≫ eSnd ≫ ieFst = leFst ≫ a₁ := by
    exact assoc₁ T'.of T.of E.B
  have hAE₂ : AE ≫ eSnd ≫ ieSnd = leSnd := by
    exact assoc₂ T'.of T.of E.B
  have hAF₀ : AF ≫ fFst = lfFst ≫ b₀ := by
    exact assoc₀ U'.of U.of F.B
  have hAF₁ : AF ≫ fSnd ≫ ifFst = lfFst ≫ b₁ := by
    exact assoc₁ U'.of U.of F.B
  have hAF₂ : AF ≫ fSnd ≫ ifSnd = lfSnd := by
    exact assoc₂ U'.of U.of F.B
  have hLE0_step1 : (leftE ≫ eFst) = (((l₀ ≫ LE) ≫ leFst) ≫ a₀) := by
    dsimp only [leftE]
    have h := (congrArg (fun q : (T'.of ⊞ T.of) ⊞ E.B ⟶ T'.of => l₀ ≫ LE ≫ q) hAE₀)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE0_step2 : (((l₀ ≫ LE) ≫ leFst) ≫ a₀) = (((l₀ ≫ vFst) ≫ v₀) ≫ a₀) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ T'.of ⊞ T.of => l₀ ≫ q ≫ a₀) hLEfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE0_step3 : (((l₀ ≫ vFst) ≫ v₀) ≫ a₀) = (((κ ≫ σ) ≫ v₀) ≫ a₀) := by
    have h := (congrArg (fun q : W ⟶ V => q ≫ v₀ ≫ a₀) hl₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE0_step4 : (((κ ≫ σ) ≫ v₀) ≫ a₀) = ((κ ≫ s₀) ≫ k₀) := by
    have h := (congrArg (fun q : S ⟶ T'.of => κ ≫ q) hσA)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE0 : (leftE ≫ eFst) = ((κ ≫ s₀) ≫ k₀) :=
    hLE0_step1.trans (hLE0_step2.trans (hLE0_step3.trans (hLE0_step4)))
  have hLE1_step1 : ((leftE ≫ eSnd) ≫ ieFst) = (((l₀ ≫ LE) ≫ leFst) ≫ a₁) := by
    dsimp only [leftE]
    have h := (congrArg (fun q : (T'.of ⊞ T.of) ⊞ E.B ⟶ T.of => l₀ ≫ LE ≫ q) hAE₁)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE1_step2 : (((l₀ ≫ LE) ≫ leFst) ≫ a₁) = (((l₀ ≫ vFst) ≫ v₀) ≫ a₁) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ T'.of ⊞ T.of => l₀ ≫ q ≫ a₁) hLEfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE1_step3 : (((l₀ ≫ vFst) ≫ v₀) ≫ a₁) = (((κ ≫ σ) ≫ v₀) ≫ a₁) := by
    have h := (congrArg (fun q : W ⟶ V => q ≫ v₀ ≫ a₁) hl₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE1_step4 : (((κ ≫ σ) ≫ v₀) ≫ a₁) = ((κ ≫ s₁) ≫ k₁) := by
    have h := (congrArg (fun q : S ⟶ T.of => κ ≫ q) hσT)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE1 : ((leftE ≫ eSnd) ≫ ieFst) = ((κ ≫ s₁) ≫ k₁) :=
    hLE1_step1.trans (hLE1_step2.trans (hLE1_step3.trans (hLE1_step4)))
  have hLE2_step1 : ((leftE ≫ eSnd) ≫ ieSnd) = ((l₀ ≫ LE) ≫ leSnd) := by
    dsimp only [leftE]
    have h := (congrArg (fun q : (T'.of ⊞ T.of) ⊞ E.B ⟶ E.B => l₀ ≫ LE ≫ q) hAE₂)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE2_step2 : ((l₀ ≫ LE) ≫ leSnd) = ((l₀ ≫ vSnd) ≫ P.fst) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ E.B => l₀ ≫ q) hLEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE2_step3 : ((l₀ ≫ vSnd) ≫ P.fst) = (π ≫ P.fst) := by
    have h := (congrArg (fun q : W ⟶ P.obj => q ≫ P.fst) hl₀snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLE2 : ((leftE ≫ eSnd) ≫ ieSnd) = (π ≫ P.fst) :=
    hLE2_step1.trans (hLE2_step2.trans (hLE2_step3))
  have hLF0_step1 : (leftF ≫ fFst) = (((l₀ ≫ LF) ≫ lfFst) ≫ b₀) := by
    dsimp only [leftF]
    have h := (congrArg (fun q : (U'.of ⊞ U.of) ⊞ F.B ⟶ U'.of => l₀ ≫ LF ≫ q) hAF₀)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF0_step2 : (((l₀ ≫ LF) ≫ lfFst) ≫ b₀) = (((l₀ ≫ vFst) ≫ v₁) ≫ b₀) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ U'.of ⊞ U.of => l₀ ≫ q ≫ b₀) hLFfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF0_step3 : (((l₀ ≫ vFst) ≫ v₁) ≫ b₀) = (((κ ≫ σ) ≫ v₁) ≫ b₀) := by
    have h := (congrArg (fun q : W ⟶ V => q ≫ v₁ ≫ b₀) hl₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF0_step4 : (((κ ≫ σ) ≫ v₁) ≫ b₀) = ((κ ≫ s₀) ≫ k₀') := by
    have h := (congrArg (fun q : S ⟶ U'.of => κ ≫ q) hσB)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF0 : (leftF ≫ fFst) = ((κ ≫ s₀) ≫ k₀') :=
    hLF0_step1.trans (hLF0_step2.trans (hLF0_step3.trans (hLF0_step4)))
  have hLF1_step1 : ((leftF ≫ fSnd) ≫ ifFst) = (((l₀ ≫ LF) ≫ lfFst) ≫ b₁) := by
    dsimp only [leftF]
    have h := (congrArg (fun q : (U'.of ⊞ U.of) ⊞ F.B ⟶ U.of => l₀ ≫ LF ≫ q) hAF₁)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF1_step2 : (((l₀ ≫ LF) ≫ lfFst) ≫ b₁) = (((l₀ ≫ vFst) ≫ v₁) ≫ b₁) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ U'.of ⊞ U.of => l₀ ≫ q ≫ b₁) hLFfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF1_step3 : (((l₀ ≫ vFst) ≫ v₁) ≫ b₁) = (((κ ≫ σ) ≫ v₁) ≫ b₁) := by
    have h := (congrArg (fun q : W ⟶ V => q ≫ v₁ ≫ b₁) hl₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF1_step4 : (((κ ≫ σ) ≫ v₁) ≫ b₁) = ((κ ≫ s₁) ≫ k₁') := by
    have h := (congrArg (fun q : S ⟶ U.of => κ ≫ q) hσU)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF1 : ((leftF ≫ fSnd) ≫ ifFst) = ((κ ≫ s₁) ≫ k₁') :=
    hLF1_step1.trans (hLF1_step2.trans (hLF1_step3.trans (hLF1_step4)))
  have hLF2_step1 : ((leftF ≫ fSnd) ≫ ifSnd) = ((l₀ ≫ LF) ≫ lfSnd) := by
    dsimp only [leftF]
    have h := (congrArg (fun q : (U'.of ⊞ U.of) ⊞ F.B ⟶ F.B => l₀ ≫ LF ≫ q) hAF₂)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF2_step2 : ((l₀ ≫ LF) ≫ lfSnd) = ((l₀ ≫ vSnd) ≫ P.snd) := by
    have h := (congrArg (fun q : V ⊞ P.obj ⟶ F.B => l₀ ≫ q) hLFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF2_step3 : ((l₀ ≫ vSnd) ≫ P.snd) = (π ≫ P.snd) := by
    have h := (congrArg (fun q : W ⟶ P.obj => q ≫ P.snd) hl₀snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hLF2 : ((leftF ≫ fSnd) ≫ ifSnd) = (π ≫ P.snd) :=
    hLF2_step1.trans (hLF2_step2.trans (hLF2_step3))
  have hRE0_step1 : (rightE ≫ eFst) = (((r₀ ≫ r₁) ≫ OE) ≫ oeFst) := by
    dsimp only [rightE]
    have h := (congrArg (fun q : T'.of ⊞ E1.B ⟶ T'.of => r₀ ≫ r₁ ≫ OE ≫ q) hMEfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE0_step2 : (((r₀ ≫ r₁) ≫ OE) ≫ oeFst) = (((r₀ ≫ r₁) ≫ qFst) ≫ k₀) := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ T'.of => r₀ ≫ r₁ ≫ q) hOEfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE0_step3 : (((r₀ ≫ r₁) ≫ qFst) ≫ k₀) = ((r₀ ≫ rFst) ≫ k₀) := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ K₀ => r₀ ≫ q ≫ k₀) hr₁fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE0_step4 : ((r₀ ≫ rFst) ≫ k₀) = ((κ ≫ s₀) ≫ k₀) := by
    have h := (congrArg (fun q : W ⟶ K₀ => q ≫ k₀) hr₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE0 : (rightE ≫ eFst) = ((κ ≫ s₀) ≫ k₀) :=
    hRE0_step1.trans (hRE0_step2.trans (hRE0_step3.trans (hRE0_step4)))
  have hRE1_step1 : ((rightE ≫ eSnd) ≫ ieFst) = (((((r₀ ≫ r₁) ≫ OE) ≫ oeSnd) ≫ cE) ≫ ieFst) := by
    dsimp only [rightE]
    have h := (congrArg (fun q : T'.of ⊞ E1.B ⟶ T.of ⊞ E.B => r₀ ≫ r₁ ≫ OE ≫ q ≫ ieFst) hMEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1_step2 : (((((r₀ ≫ r₁) ≫ OE) ≫ oeSnd) ≫ cE) ≫ ieFst) =
      (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.fst) ≫ cE) ≫ ieFst) := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ E1.B => r₀ ≫ r₁ ≫ q ≫ cE ≫ ieFst) hOEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1_step3 : (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.fst) ≫ cE) ≫ ieFst) =
      (((((r₀ ≫ rSnd) ≫ m) ≫ Q.fst) ≫ cE) ≫ ieFst) := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ Q.obj => r₀ ≫ q ≫ Q.fst ≫ cE ≫ ieFst) hr₁snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1_step4 : (((((r₀ ≫ rSnd) ≫ m) ≫ Q.fst) ≫ cE) ≫ ieFst) =
      (((r₀ ≫ rSnd) ≫ IE) ≫ ieFst) := by
    have h := (congrArg (fun q : D₀ ⟶ T.of ⊞ E.B => r₀ ≫ rSnd ≫ q ≫ ieFst) hInnerE)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1_step5 : (((r₀ ≫ rSnd) ≫ IE) ≫ ieFst) = (((r₀ ≫ rSnd) ≫ dFst) ≫ k₁) := by
    have h := (congrArg (fun q : D₀ ⟶ T.of => r₀ ≫ rSnd ≫ q) hIEfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1_step6 : (((r₀ ≫ rSnd) ≫ dFst) ≫ k₁) = ((κ ≫ s₁) ≫ k₁) := by
    have h := (congrArg (fun q : W ⟶ K₁ => q ≫ k₁) hr₀ker)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE1 : ((rightE ≫ eSnd) ≫ ieFst) = ((κ ≫ s₁) ≫ k₁) :=
    hRE1_step1.trans (hRE1_step2.trans (hRE1_step3.trans (hRE1_step4.trans (hRE1_step5.trans
        (hRE1_step6)))))
  have hRE2_step1 : ((rightE ≫ eSnd) ≫ ieSnd) = (((((r₀ ≫ r₁) ≫ OE) ≫ oeSnd) ≫ cE) ≫ ieSnd) := by
    dsimp only [rightE]
    have h := (congrArg (fun q : T'.of ⊞ E1.B ⟶ T.of ⊞ E.B => r₀ ≫ r₁ ≫ OE ≫ q ≫ ieSnd) hMEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2_step2 : (((((r₀ ≫ r₁) ≫ OE) ≫ oeSnd) ≫ cE) ≫ ieSnd) =
      (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.fst) ≫ cE) ≫ ieSnd) := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ E1.B => r₀ ≫ r₁ ≫ q ≫ cE ≫ ieSnd) hOEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2_step3 : (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.fst) ≫ cE) ≫ ieSnd) =
      (((((r₀ ≫ rSnd) ≫ m) ≫ Q.fst) ≫ cE) ≫ ieSnd) := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ Q.obj => r₀ ≫ q ≫ Q.fst ≫ cE ≫ ieSnd) hr₁snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2_step4 : (((((r₀ ≫ rSnd) ≫ m) ≫ Q.fst) ≫ cE) ≫ ieSnd) =
      (((r₀ ≫ rSnd) ≫ IE) ≫ ieSnd) := by
    have h := (congrArg (fun q : D₀ ⟶ T.of ⊞ E.B => r₀ ≫ rSnd ≫ q ≫ ieSnd) hInnerE)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2_step5 : (((r₀ ≫ rSnd) ≫ IE) ≫ ieSnd) = (((r₀ ≫ rSnd) ≫ dSnd) ≫ P.fst) := by
    have h := (congrArg (fun q : D₀ ⟶ E.B => r₀ ≫ rSnd ≫ q) hIEsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2_step6 : (((r₀ ≫ rSnd) ≫ dSnd) ≫ P.fst) = (π ≫ P.fst) := by
    have h := (congrArg (fun q : W ⟶ P.obj => q ≫ P.fst) hr₀pb)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRE2 : ((rightE ≫ eSnd) ≫ ieSnd) = (π ≫ P.fst) :=
    hRE2_step1.trans (hRE2_step2.trans (hRE2_step3.trans (hRE2_step4.trans (hRE2_step5.trans
        (hRE2_step6)))))
  have hRF0_step1 : (rightF ≫ fFst) = (((r₀ ≫ r₁) ≫ OF) ≫ ofFst) := by
    dsimp only [rightF]
    have h := (congrArg (fun q : U'.of ⊞ F1.B ⟶ U'.of => r₀ ≫ r₁ ≫ OF ≫ q) hMFfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF0_step2 : (((r₀ ≫ r₁) ≫ OF) ≫ ofFst) = (((r₀ ≫ r₁) ≫ qFst) ≫ k₀') := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ U'.of => r₀ ≫ r₁ ≫ q) hOFfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF0_step3 : (((r₀ ≫ r₁) ≫ qFst) ≫ k₀') = ((r₀ ≫ rFst) ≫ k₀') := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ K₀ => r₀ ≫ q ≫ k₀') hr₁fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF0_step4 : ((r₀ ≫ rFst) ≫ k₀') = ((κ ≫ s₀) ≫ k₀') := by
    have h := (congrArg (fun q : W ⟶ K₀ => q ≫ k₀') hr₀fst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF0 : (rightF ≫ fFst) = ((κ ≫ s₀) ≫ k₀') :=
    hRF0_step1.trans (hRF0_step2.trans (hRF0_step3.trans (hRF0_step4)))
  have hRF1_step1 : ((rightF ≫ fSnd) ≫ ifFst) = (((((r₀ ≫ r₁) ≫ OF) ≫ ofSnd) ≫ cF) ≫ ifFst) := by
    dsimp only [rightF]
    have h := (congrArg (fun q : U'.of ⊞ F1.B ⟶ U.of ⊞ F.B => r₀ ≫ r₁ ≫ OF ≫ q ≫ ifFst) hMFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1_step2 : (((((r₀ ≫ r₁) ≫ OF) ≫ ofSnd) ≫ cF) ≫ ifFst) =
      (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.snd) ≫ cF) ≫ ifFst) := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ F1.B => r₀ ≫ r₁ ≫ q ≫ cF ≫ ifFst) hOFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1_step3 : (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.snd) ≫ cF) ≫ ifFst) =
      (((((r₀ ≫ rSnd) ≫ m) ≫ Q.snd) ≫ cF) ≫ ifFst) := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ Q.obj => r₀ ≫ q ≫ Q.snd ≫ cF ≫ ifFst) hr₁snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1_step4 : (((((r₀ ≫ rSnd) ≫ m) ≫ Q.snd) ≫ cF) ≫ ifFst) =
      (((r₀ ≫ rSnd) ≫ IF) ≫ ifFst) := by
    have h := (congrArg (fun q : D₀ ⟶ U.of ⊞ F.B => r₀ ≫ rSnd ≫ q ≫ ifFst) hInnerF)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1_step5 : (((r₀ ≫ rSnd) ≫ IF) ≫ ifFst) = (((r₀ ≫ rSnd) ≫ dFst) ≫ k₁') := by
    have h := (congrArg (fun q : D₀ ⟶ U.of => r₀ ≫ rSnd ≫ q) hIFfst)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1_step6 : (((r₀ ≫ rSnd) ≫ dFst) ≫ k₁') = ((κ ≫ s₁) ≫ k₁') := by
    have h := (congrArg (fun q : W ⟶ K₁ => q ≫ k₁') hr₀ker)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF1 : ((rightF ≫ fSnd) ≫ ifFst) = ((κ ≫ s₁) ≫ k₁') :=
    hRF1_step1.trans (hRF1_step2.trans (hRF1_step3.trans (hRF1_step4.trans (hRF1_step5.trans
        (hRF1_step6)))))
  have hRF2_step1 : ((rightF ≫ fSnd) ≫ ifSnd) = (((((r₀ ≫ r₁) ≫ OF) ≫ ofSnd) ≫ cF) ≫ ifSnd) := by
    dsimp only [rightF]
    have h := (congrArg (fun q : U'.of ⊞ F1.B ⟶ U.of ⊞ F.B => r₀ ≫ r₁ ≫ OF ≫ q ≫ ifSnd) hMFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2_step2 : (((((r₀ ≫ r₁) ≫ OF) ≫ ofSnd) ≫ cF) ≫ ifSnd) =
      (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.snd) ≫ cF) ≫ ifSnd) := by
    have h := (congrArg (fun q : K₀ ⊞ Q.obj ⟶ F1.B => r₀ ≫ r₁ ≫ q ≫ cF ≫ ifSnd) hOFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2_step3 : (((((r₀ ≫ r₁) ≫ qSnd) ≫ Q.snd) ≫ cF) ≫ ifSnd) =
      (((((r₀ ≫ rSnd) ≫ m) ≫ Q.snd) ≫ cF) ≫ ifSnd) := by
    have h := (congrArg (fun q : K₀ ⊞ D₀ ⟶ Q.obj => r₀ ≫ q ≫ Q.snd ≫ cF ≫ ifSnd) hr₁snd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2_step4 : (((((r₀ ≫ rSnd) ≫ m) ≫ Q.snd) ≫ cF) ≫ ifSnd) =
      (((r₀ ≫ rSnd) ≫ IF) ≫ ifSnd) := by
    have h := (congrArg (fun q : D₀ ⟶ U.of ⊞ F.B => r₀ ≫ rSnd ≫ q ≫ ifSnd) hInnerF)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2_step5 : (((r₀ ≫ rSnd) ≫ IF) ≫ ifSnd) = (((r₀ ≫ rSnd) ≫ dSnd) ≫ P.snd) := by
    have h := (congrArg (fun q : D₀ ⟶ F.B => r₀ ≫ rSnd ≫ q) hIFsnd)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2_step6 : (((r₀ ≫ rSnd) ≫ dSnd) ≫ P.snd) = (π ≫ P.snd) := by
    have h := (congrArg (fun q : W ⟶ P.obj => q ≫ P.snd) hr₀pb)
    simp only [Category.assoc] at h ⊢
    exact h
  have hRF2 : ((rightF ≫ fSnd) ≫ ifSnd) = (π ≫ P.snd) :=
    hRF2_step1.trans (hRF2_step2.trans (hRF2_step3.trans (hRF2_step4.trans (hRF2_step5.trans
        (hRF2_step6)))))
  have hNativeE : l₀ ≫ actionConvolutionFirst (T' ⊗ T) (U' ⊗ U) E F ≫
      (biprod.associator T'.of T.of E.B).hom =
    r₀ ≫ r₁ ≫ actionConvolutionFirst T' U' E1 F1 ≫
      biprod.map (𝟙 T'.of) (eqToIso (leftSumObj_middle_eq T E)).hom := by
    change leftE = rightE
    apply biprod.hom_ext
    · exact hLE0.trans hRE0.symm
    · apply biprod.hom_ext
      · have h := hLE1.trans hRE1.symm
        simp only [Category.assoc] at h ⊢
        exact h
      · have h := hLE2.trans hRE2.symm
        simp only [Category.assoc] at h ⊢
        exact h
  have hNativeF : l₀ ≫ actionConvolutionSecond (T' ⊗ T) (U' ⊗ U) E F ≫
      (biprod.associator U'.of U.of F.B).hom =
    r₀ ≫ r₁ ≫ actionConvolutionSecond T' U' E1 F1 ≫
      biprod.map (𝟙 U'.of) (eqToIso (leftSumObj_middle_eq U F)).hom := by
    change leftF = rightF
    apply biprod.hom_ext
    · exact hLF0.trans hRF0.symm
    · apply biprod.hom_ext
      · have h := hLF1.trans hRF1.symm
        simp only [Category.assoc] at h ⊢
        exact h
      · have h := hLF2.trans hRF2.symm
        simp only [Category.assoc] at h ⊢
        exact h
  apply Z.square.hom_ext
  · apply (cancel_mono eE.hom).mp
    have hL := congrArg (fun q : ((T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)) ⊞ P.obj ⟶
      T'.of ⊞ (T.of ⊞ E.B) => l₀ ≫ q) hLeftE
    have hR := congrArg (fun q : (T'.of ⊞ U'.of) ⊞ Q.obj ⟶
      T'.of ⊞ (T.of ⊞ E.B) => r₀ ≫ r₁ ≫ q) hRightE
    simpa only [l₀, l₁, l₂, r₀, r₁, r₂, Category.assoc] using
      hL.trans (hNativeE.trans hR.symm)
  · apply (cancel_mono eF.hom).mp
    have hL := congrArg (fun q : ((T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)) ⊞ P.obj ⟶
      U'.of ⊞ (U.of ⊞ F.B) => l₀ ≫ q) hLeftF
    have hR := congrArg (fun q : (T'.of ⊞ U'.of) ⊞ Q.obj ⟶
      U'.of ⊞ (U.of ⊞ F.B) => r₀ ≫ r₁ ≫ q) hRightF
    simpa only [l₀, l₁, l₂, r₀, r₁, r₂, Category.assoc] using
      hL.trans (hNativeF.trans hR.symm)

theorem actionConvolution_assoc (T' U' T U : Core C) (E F : FixedTargetExtension C X) :
    FixedTargetExtension.leftSumMap (stabilizerExchange T' U' T U).hom
        (𝟙 (convolutionObj E F)) ≫
        (actionConvolutionIso (T' ⊗ T) (U' ⊗ U) E F).hom ≫
        convolutionMap (FixedTargetExtension.leftSumAssocIso T' T E).hom
          (FixedTargetExtension.leftSumAssocIso U' U F).hom =
      (FixedTargetExtension.leftSumAssocIso (T' ⊗ U') (T ⊗ U) (convolutionObj E F)).hom ≫
        FixedTargetExtension.leftSumMap (𝟙 (T' ⊗ U')) (actionConvolutionIso T U E F).hom ≫
        (actionConvolutionIso T' U' (FixedTargetExtension.leftSumObj T E)
          (FixedTargetExtension.leftSumObj U F)).hom := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  let Q := convolutionObj E F
  let P := convolutionPullback E F
  let T0 := T' ⊗ U'
  let U0 := T ⊗ U
  let E1 := FixedTargetExtension.leftSumObj T E
  let F1 := FixedTargetExtension.leftSumObj U F
  let A1 := FixedTargetExtension.leftSumMap (stabilizerExchange T' U' T U).hom (𝟙 Q)
  let A2 := (actionConvolutionIso (T' ⊗ T) (U' ⊗ U) E F).hom
  let A3 := convolutionMap (FixedTargetExtension.leftSumAssocIso T' T E).hom
    (FixedTargetExtension.leftSumAssocIso U' U F).hom
  let B1 := (FixedTargetExtension.leftSumAssocIso T0 U0 Q).hom
  let B2 := FixedTargetExtension.leftSumMap (𝟙 T0) (actionConvolutionIso T U E F).hom
  let B3 := (actionConvolutionIso T' U' E1 F1).hom
  let l := A1 ≫ A2 ≫ A3
  let r := B1 ≫ B2 ≫ B3
  let lc := biprod.map (exchangeIso T'.of U'.of T.of U.of).hom (𝟙 P.obj) ≫
    actionConvolutionMiddle (T' ⊗ T) (U' ⊗ U) E F ≫
    convolutionMiddleMap (FixedTargetExtension.leftSumAssocIso T' T E).hom
      (FixedTargetExtension.leftSumAssocIso U' U F).hom
  let rc := (biprod.associator (T'.of ⊞ U'.of) (T.of ⊞ U.of) P.obj).hom ≫
    biprod.map (𝟙 (T'.of ⊞ U'.of)) (actionConvolutionMiddle T U E F) ≫
    actionConvolutionMiddle T' U' E1 F1
  have hP : Q.B = P.obj := convolutionObj_middle_eq E F
  have hS : (FixedTargetExtension.leftSumObj (T0 ⊗ U0) Q).B =
      (((T'.of ⊞ U'.of) ⊞ (T.of ⊞ U.of)) ⊞ P.obj) := rfl
  have hL1 : (FixedTargetExtension.leftSumObj ((T' ⊗ T) ⊗ (U' ⊗ U)) Q).B =
      (((T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)) ⊞ P.obj) := rfl
  have hL2 := convolutionObj_middle_eq (FixedTargetExtension.leftSumObj (T' ⊗ T) E)
    (FixedTargetExtension.leftSumObj (U' ⊗ U) F)
  have hZ := convolutionObj_middle_eq (FixedTargetExtension.leftSumObj T' E1)
    (FixedTargetExtension.leftSumObj U' F1)
  have hR1 : (FixedTargetExtension.leftSumObj T0
      (FixedTargetExtension.leftSumObj U0 Q)).B =
      ((T'.of ⊞ U'.of) ⊞ ((T.of ⊞ U.of) ⊞ P.obj)) := rfl
  have hR2 : (FixedTargetExtension.leftSumObj T0 (convolutionObj E1 F1)).B =
      ((T'.of ⊞ U'.of) ⊞ (convolutionPullback E1 F1).obj) := rfl
  have hT0 : T0.of = (T'.of ⊞ U'.of) := rfl
  have hU0 : U0.of = (T.of ⊞ U.of) := rfl
  have hl : HEq l.b.hom lc := by
    have hCoreS : (T0 ⊗ U0).of =
        ((T'.of ⊞ U'.of) ⊞ (T.of ⊞ U.of)) := rfl
    have hCoreT : ((T' ⊗ T) ⊗ (U' ⊗ U)).of =
        ((T'.of ⊞ T.of) ⊞ (U'.of ⊞ U.of)) := rfl
    have hIdOld : (𝟙 Q : Q ⟶ Q).b.hom = 𝟙 Q.B := by
      simp only [FixedTargetExtension.id_b, Iso.refl_hom]
    have hId := (heq_of_eq hIdOld).trans
      ((eqToHom_heq_id_dom Q.B P.obj hP).symm.trans
        (eqToHom_heq_id_cod Q.B P.obj hP))
    have hMap := biprod_map_heq hCoreS hCoreT hP hP
      (heq_of_eq (stabilizerExchange_hom T' U' T U)) hId
    have hA1 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
      (stabilizerExchange T' U' T U).hom (𝟙 Q))).trans hMap
    have hA2 := heq_of_eq (actionConvolutionIso_middle (T' ⊗ T) (U' ⊗ U) E F)
    have hA3 := heq_of_eq (convolutionMap_middle
      (FixedTargetExtension.leftSumAssocIso T' T E).hom
      (FixedTargetExtension.leftSumAssocIso U' U F).hom)
    have h23 := heq_comp hL1 hL2 hZ hA2 hA3
    have h123 := heq_comp hS hL1 hZ hA1 h23
    have hRow : l.b.hom = A1.b.hom ≫ A2.b.hom ≫ A3.b.hom := by
      simp only [l, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h123
  have hr : HEq r.b.hom rc := by
    have hAssoc := biprod_assoc_hom_heq hT0 hU0 hP
    have hB1 := (heq_of_eq (FixedTargetExtension.leftSumAssocIso_b_hom T0 U0 Q)).trans
      hAssoc
    have hIdOld : (𝟙 T0 : T0 ⟶ T0).iso.hom = 𝟙 T0.of := rfl
    have hId := (heq_of_eq hIdOld).trans
      ((eqToHom_heq_id_dom T0.of (T'.of ⊞ U'.of) hT0).symm.trans
        (eqToHom_heq_id_cod T0.of (T'.of ⊞ U'.of) hT0))
    have hMap := biprod_map_heq hT0 hT0 (leftSumTensor_middle_eq T U E F)
      (convolutionObj_middle_eq E1 F1) hId
      (heq_of_eq (actionConvolutionIso_middle T U E F))
    have hB2 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom (𝟙 T0)
      (actionConvolutionIso T U E F).hom)).trans hMap
    have hB3 := heq_of_eq (actionConvolutionIso_middle T' U' E1 F1)
    have h23 := heq_comp hR1 hR2 hZ hB2 hB3
    have h123 := heq_comp hS hR1 hZ hB1 h23
    have hRow : r.b.hom = B1.b.hom ≫ B2.b.hom ≫ B3.b.hom := by
      simp only [r, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h123
  exact eq_of_heq (hl.trans ((heq_of_eq
    (actionConvolution_assoc_canonical T' U' T U E F)).trans hr.symm))

/-- Unit compatibility uses the actual zero⊞zero stabilizer Iso and original action units. -/
private theorem unitRow_middle_eq (E F : FixedTargetExtension C X) :
    ((FixedTargetExtension.leftSumObj (𝟙_ (Core C)) (convolutionObj E F)).B) =
      ((0 : C) ⊞ (convolutionPullback E F).obj) := by rfl

omit [ExactCategory C] in
private theorem unitCore_hom :
    ((λ_ (𝟙_ (Core C))).hom).iso.hom =
      (biprod.snd : (0 : C) ⊞ (0 : C) ⟶ (0 : C)) := rfl

@[reassoc]
private theorem leftSumUnit_middle_native (E : FixedTargetExtension C X) :
    (eqToIso (leftSumObj_middle_eq (𝟙_ (Core C)) E)).inv ≫
      (FixedTargetExtension.leftSumUnitIso E).hom.b.hom =
        (biprod.snd : (0 : C) ⊞ E.B ⟶ E.B) := by
  let j : (FixedTargetExtension.leftSumObj (𝟙_ (Core C)) E).B ⟶ E.B :=
    (FixedTargetExtension.leftSumUnitIso E).hom.b.hom
  let n : (0 : C) ⊞ E.B ⟶ E.B := biprod.snd
  have hField : HEq j n := by
    exact heq_of_eq (FixedTargetExtension.leftSumUnitIso_b_hom E)
  have h := (conj_eqToHom_iff_heq j n
    (leftSumObj_middle_eq (𝟙_ (Core C)) E) (rfl : E.B = E.B)).2 hField
  have hj : j = (eqToIso (leftSumObj_middle_eq (𝟙_ (Core C)) E)).hom ≫ n := by
    simpa only [eqToIso.hom, eqToHom_refl, Category.comp_id] using h
  change (eqToIso (leftSumObj_middle_eq (𝟙_ (Core C)) E)).inv ≫ j = n
  rw [hj]
  simp only [Iso.inv_hom_id_assoc]

private theorem actionConvolution_unit_canonical (E F : FixedTargetExtension C X) :
    biprod.map (biprod.snd : (0 : C) ⊞ (0 : C) ⟶ (0 : C))
        (𝟙 (convolutionPullback E F).obj) ≫
        (biprod.snd : (0 : C) ⊞ (convolutionPullback E F).obj ⟶
          (convolutionPullback E F).obj) =
      actionConvolutionMiddle (𝟙_ (Core C)) (𝟙_ (Core C)) E F ≫
        convolutionMiddleMap (FixedTargetExtension.leftSumUnitIso E).hom
          (FixedTargetExtension.leftSumUnitIso F).hom := by
  apply (convolutionPullback E F).square.hom_ext
  · rw [Category.assoc, biprod.map_snd_assoc, Category.id_comp,
      Category.assoc, convolutionMiddleMap_fst,
      actionConvolutionMiddle_first_assoc, leftSumUnit_middle_native]
    exact (biprod.lift_snd _ _).symm
  · rw [Category.assoc, biprod.map_snd_assoc, Category.id_comp,
      Category.assoc, convolutionMiddleMap_snd,
      actionConvolutionMiddle_second_assoc, leftSumUnit_middle_native]
    exact (biprod.lift_snd _ _).symm

theorem actionConvolution_unit (E F : FixedTargetExtension C X) :
    FixedTargetExtension.leftSumMap (λ_ (𝟙_ (Core C))).hom (𝟙 (convolutionObj E F)) ≫
        (FixedTargetExtension.leftSumUnitIso (convolutionObj E F)).hom =
      (actionConvolutionIso (𝟙_ (Core C)) (𝟙_ (Core C)) E F).hom ≫
        convolutionMap (FixedTargetExtension.leftSumUnitIso E).hom
          (FixedTargetExtension.leftSumUnitIso F).hom := by
  let I : Core C := 𝟙_ (Core C)
  let Q := convolutionObj E F
  let S := FixedTargetExtension.leftSumObj (I ⊗ I) Q
  let M := FixedTargetExtension.leftSumObj I Q
  let N := convolutionObj (FixedTargetExtension.leftSumObj I E)
    (FixedTargetExtension.leftSumObj I F)
  let P := convolutionPullback E F
  let P1 := convolutionPullback (FixedTargetExtension.leftSumObj I E)
    (FixedTargetExtension.leftSumObj I F)
  let a : S ⟶ M := FixedTargetExtension.leftSumMap (λ_ I).hom (𝟙 Q)
  let b : M ⟶ Q := (FixedTargetExtension.leftSumUnitIso Q).hom
  let c : S ⟶ N := (actionConvolutionIso I I E F).hom
  let d : N ⟶ Q := convolutionMap (FixedTargetExtension.leftSumUnitIso E).hom
    (FixedTargetExtension.leftSumUnitIso F).hom
  let ac : ((0 : C) ⊞ (0 : C)) ⊞ P.obj ⟶ (0 : C) ⊞ P.obj :=
    biprod.map biprod.snd (𝟙 P.obj)
  let bc : (0 : C) ⊞ P.obj ⟶ P.obj := biprod.snd
  let cc : ((0 : C) ⊞ (0 : C)) ⊞ P.obj ⟶ P1.obj := actionConvolutionMiddle I I E F
  let dc : P1.obj ⟶ P.obj := convolutionMiddleMap
    (FixedTargetExtension.leftSumUnitIso E).hom (FixedTargetExtension.leftSumUnitIso F).hom
  have hA : HEq a.b.hom ac := by
    have hu : HEq ((λ_ I).hom).iso.hom
        (biprod.snd : (0 : C) ⊞ (0 : C) ⟶ (0 : C)) := heq_of_eq (unitCore_hom (C := C))
    have hid : HEq (𝟙 Q.B) (𝟙 P.obj) := by rfl
    have hm := biprod_map_heq (rfl : (I ⊗ I).of = ((0 : C) ⊞ (0 : C)))
      (rfl : I.of = (0 : C)) (convolutionObj_middle_eq E F)
      (convolutionObj_middle_eq E F) hu hid
    let aOld : S.B ⟶ M.B := a.b.hom
    let aNative : ((I ⊗ I).of ⊞ Q.B) ⟶ (I.of ⊞ Q.B) :=
      biprod.map ((λ_ I).hom).iso.hom (𝟙 Q.B)
    have hField : HEq aOld aNative := by rfl
    exact hField.trans hm
  have hB : HEq b.b.hom bc := by
    let bo : M.B ⟶ Q.B := biprod.snd
    have h₀ : HEq b.b.hom bo := heq_of_eq (FixedTargetExtension.leftSumUnitIso_b_hom Q)
    have h₁ : HEq bo bc := by rfl
    exact h₀.trans h₁
  have hC : HEq c.b.hom cc := heq_of_eq (actionConvolutionIso_middle I I E F)
  have hD : HEq d.b.hom dc := heq_of_eq (convolutionMap_middle
    (FixedTargetExtension.leftSumUnitIso E).hom (FixedTargetExtension.leftSumUnitIso F).hom)
  have hL := heq_comp (leftSumTensor_middle_eq I I E F) (unitRow_middle_eq E F)
    (convolutionObj_middle_eq E F) hA hB
  have hR := heq_comp (leftSumTensor_middle_eq I I E F)
    (convolutionObj_middle_eq (FixedTargetExtension.leftSumObj I E)
      (FixedTargetExtension.leftSumObj I F)) (convolutionObj_middle_eq E F) hC hD
  have hlc : HEq (a ≫ b).b.hom (ac ≫ bc) := by
    exact (heq_of_eq (congrArg Iso.hom (FixedTargetExtension.comp_b a b))).trans hL
  have hrc : HEq (c ≫ d).b.hom (cc ≫ dc) := by
    exact (heq_of_eq (congrArg Iso.hom (FixedTargetExtension.comp_b c d))).trans hR
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  exact eq_of_heq (hlc.trans
    ((heq_of_eq (actionConvolution_unit_canonical E F)).trans hrc.symm))

/-- The raw product preserves the two original stabilizers as their actual tensor. -/
def auxProductRaw {a a' b b' : Auxiliary C X} (r : RawHom a a') (s : RawHom b b') :
    RawHom (⟨convolutionObj a.of b.of⟩ : Auxiliary C X) ⟨convolutionObj a'.of b'.of⟩ where
  stabilizer := r.stabilizer ⊗ s.stabilizer
  hom := (actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫
    convolutionMap r.hom s.hom

/-- Its forward middle follows the actual two stabilized original row maps. -/
theorem auxProductRaw_middle {a a' b b' : Auxiliary C X}
    (r : RawHom a a') (s : RawHom b b') :
    (auxProductRaw r s).hom.b.hom =
      actionConvolutionMiddle r.stabilizer s.stabilizer a.of b.of ≫
        convolutionMiddleMap r.hom s.hom := rfl

/-- Tensoring the genuine stabilizer-change Isos preserves the original quotient relation. -/
theorem auxProductRaw_rel {a a' b b' : Auxiliary C X}
    {r r' : RawHom a a'} {s s' : RawHom b b'} (hr : r.Rel r') (hs : s.Rel s') :
    (auxProductRaw r s).Rel (auxProductRaw r' s') := by
  obtain ⟨e, he⟩ := hr
  obtain ⟨d, hd⟩ := hs
  refine ⟨tensorIso e d, ?_⟩
  have hθ : FixedTargetExtension.leftSumMap (e.hom ⊗ₘ d.hom)
        (𝟙 (convolutionObj a.of b.of)) ≫
        (actionConvolutionIso r'.stabilizer s'.stabilizer a.of b.of).hom =
      (actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫
        convolutionMap (FixedTargetExtension.leftSumMap e.hom (𝟙 a.of))
          (FixedTargetExtension.leftSumMap d.hom (𝟙 b.of)) := by
    simpa only [convolutionMap_id] using
      actionConvolutionIso_natural e.hom d.hom (𝟙 a.of) (𝟙 b.of)
  have he' : FixedTargetExtension.leftSumMap e.hom (𝟙 a.of) ≫ r'.hom = r.hom := he
  have hd' : FixedTargetExtension.leftSumMap d.hom (𝟙 b.of) ≫ s'.hom = s.hom := hd
  change FixedTargetExtension.leftSumMap (e.hom ⊗ₘ d.hom)
        (𝟙 (convolutionObj a.of b.of)) ≫
        ((actionConvolutionIso r'.stabilizer s'.stabilizer a.of b.of).hom ≫
          convolutionMap r'.hom s'.hom) =
      (actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫
        convolutionMap r.hom s.hom
  calc
    _ = ((actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫
        convolutionMap (FixedTargetExtension.leftSumMap e.hom (𝟙 a.of))
          (FixedTargetExtension.leftSumMap d.hom (𝟙 b.of))) ≫
          convolutionMap r'.hom s'.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ convolutionMap r'.hom s'.hom) hθ)
    _ = (actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫
        convolutionMap (FixedTargetExtension.leftSumMap e.hom (𝟙 a.of) ≫ r'.hom)
          (FixedTargetExtension.leftSumMap d.hom (𝟙 b.of) ≫ s'.hom) :=
      (Category.assoc _ _ _).trans (congrArg
        ((actionConvolutionIso r.stabilizer s.stabilizer a.of b.of).hom ≫ ·)
          (convolutionMap_comp _ _ _ _).symm)
    _ = _ := by rw [he', hd']

/-- The raw product of identities is the original identity modulo its actual unit Iso. -/
theorem auxProductRaw_id (a b : Auxiliary C X) :
    (auxProductRaw (RawHom.id a) (RawHom.id b)).Rel
      (RawHom.id (⟨convolutionObj a.of b.of⟩ : Auxiliary C X)) := by
  refine ⟨λ_ (𝟙_ (Core C)), ?_⟩
  exact actionConvolution_unit a.of b.of

/-- Composition keeps both later-times-earlier stabilizers, with their actual exchange Iso. -/
theorem auxProductRaw_comp {a a' a'' b b' b'' : Auxiliary C X}
    (r : RawHom a a') (r' : RawHom a' a'') (s : RawHom b b') (s' : RawHom b' b'') :
    ((auxProductRaw r s).comp (auxProductRaw r' s')).Rel
      (auxProductRaw (r.comp r') (s.comp s')) := by
  let P := r'.stabilizer
  let Q := s'.stabilizer
  let T := r.stabilizer
  let U := s.stabilizer
  let M := P ⊗ Q
  let ar := (FixedTargetExtension.leftSumAssocIso P T a.of).hom
  let as' := (FixedTargetExtension.leftSumAssocIso Q U b.of).hom
  let lr := FixedTargetExtension.leftSumMap (𝟙 P) r.hom
  let ls := FixedTargetExtension.leftSumMap (𝟙 Q) s.hom
  let θ := (actionConvolutionIso T U a.of b.of).hom
  let θ' := (actionConvolutionIso P Q a'.of b'.of).hom
  let θs := (actionConvolutionIso P Q (r.stabilizer ⊙ₗ a.of)
    (s.stabilizer ⊙ₗ b.of)).hom
  let A := (FixedTargetExtension.leftSumAssocIso M (T ⊗ U)
    (convolutionObj a.of b.of)).hom
  refine ⟨stabilizerExchange P Q T U, ?_⟩
  have hn : θs ≫ convolutionMap lr ls =
      FixedTargetExtension.leftSumMap (𝟙 M) (convolutionMap r.hom s.hom) ≫ θ' := by
    simpa only [MonoidalCategory.id_tensorHom_id, FixedTargetExtension.leftSumAction] using
      (actionConvolutionIso_natural (𝟙 P) (𝟙 Q) r.hom s.hom).symm
  have hc : FixedTargetExtension.leftSumMap (𝟙 M) θ ≫
        FixedTargetExtension.leftSumMap (𝟙 M) (convolutionMap r.hom s.hom) =
      FixedTargetExtension.leftSumMap (𝟙 M) (θ ≫ convolutionMap r.hom s.hom) := by
    simpa only [Category.comp_id] using
      (FixedTargetExtension.leftSumMap_comp (𝟙 M) (𝟙 M) θ
        (convolutionMap r.hom s.hom)).symm
  change FixedTargetExtension.leftSumMap (stabilizerExchange P Q T U).hom
        (𝟙 (convolutionObj a.of b.of)) ≫
        ((actionConvolutionIso (P ⊗ T) (Q ⊗ U) a.of b.of).hom ≫
          convolutionMap (ar ≫ lr ≫ r'.hom) (as' ≫ ls ≫ s'.hom)) =
      A ≫ FixedTargetExtension.leftSumMap (𝟙 M) (θ ≫ convolutionMap r.hom s.hom) ≫
        θ' ≫ convolutionMap r'.hom s'.hom
  calc
    _ = (FixedTargetExtension.leftSumMap (stabilizerExchange P Q T U).hom
          (𝟙 (convolutionObj a.of b.of)) ≫
          (actionConvolutionIso (P ⊗ T) (Q ⊗ U) a.of b.of).hom ≫
          convolutionMap ar as') ≫ convolutionMap lr ls ≫
          convolutionMap r'.hom s'.hom := by
      simp only [convolutionMap_comp, Category.assoc]
    _ = (A ≫ FixedTargetExtension.leftSumMap (𝟙 M) θ ≫ θs) ≫
        convolutionMap lr ls ≫ convolutionMap r'.hom s'.hom :=
      congrArg (fun k => k ≫ convolutionMap lr ls ≫ convolutionMap r'.hom s'.hom)
        (actionConvolution_assoc P Q T U a.of b.of)
    _ = A ≫ FixedTargetExtension.leftSumMap (𝟙 M) θ ≫
        (FixedTargetExtension.leftSumMap (𝟙 M) (convolutionMap r.hom s.hom) ≫ θ') ≫
          convolutionMap r'.hom s'.hom := by
      simpa only [Category.assoc] using
        congrArg (fun q => A ≫ FixedTargetExtension.leftSumMap (𝟙 M) θ ≫
          q ≫ convolutionMap r'.hom s'.hom) hn
    _ = A ≫ FixedTargetExtension.leftSumMap (𝟙 M)
        (θ ≫ convolutionMap r.hom s.hom) ≫ θ' ≫ convolutionMap r'.hom s'.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => A ≫ k ≫ θ' ≫ convolutionMap r'.hom s'.hom) hc

/-- The actual raw product descends through both original quotient relations. -/
def auxProductMap {a a' b b' : Auxiliary C X} (f : a ⟶ a') (g : b ⟶ b') :
    (⟨convolutionObj a.of b.of⟩ : Auxiliary C X) ⟶ ⟨convolutionObj a'.of b'.of⟩ :=
  Quotient.map₂ auxProductRaw (by
    intro _ _ hr _ _ hs
    exact auxProductRaw_rel hr hs) f g

@[simp]
theorem auxProductMap_mk {a a' b b' : Auxiliary C X}
    (r : RawHom a a') (s : RawHom b b') :
    auxProductMap (MonoidalActionCategory.Hom.mk r) (MonoidalActionCategory.Hom.mk s) =
      MonoidalActionCategory.Hom.mk (auxProductRaw r s) := rfl

/-- The auxiliary product functor has the original convolved rows as objects. -/
def auxiliaryProduct : Auxiliary C X × Auxiliary C X ⥤ Auxiliary C X where
  obj p := ⟨convolutionObj p.1.of p.2.of⟩
  map {p q} f := auxProductMap f.1 f.2
  map_id p := by
    exact _root_.Quotient.sound (auxProductRaw_id p.1 p.2)
  map_comp {p q t} f g := by
    rcases f with ⟨f₁, f₂⟩
    rcases g with ⟨g₁, g₂⟩
    refine Quotient.inductionOn₂ f₁ g₁ ?_
    intro r r'
    refine Quotient.inductionOn₂ f₂ g₂ ?_
    intro s s'
    exact (_root_.Quotient.sound (auxProductRaw_comp r r' s s')).symm

end AlgebraicKTheory.AuxiliaryExtension

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

@[simp]
theorem convolutionSelfPullback (E : FixedTargetExtension C X) :
    convolutionPullback E E = selfPullback E := rfl

theorem convolutionSelfObj (E : FixedTargetExtension C X) :
    convolutionObj E E = selfConvolution E := rfl

/-- The same actual diagonal representative, with the convolved-row target written explicitly. -/
def convolutionDiagonalRaw (E : FixedTargetExtension C X) :
    RawHom (⟨E⟩ : Auxiliary C X) ⟨convolutionObj E E⟩ := diagonalRaw E

@[simp]
theorem convolutionDiagonalRaw_middle (E : FixedTargetExtension C X) :
    (convolutionDiagonalRaw E).hom.b.hom = middleForward E := rfl

omit [HasZeroObject C] [ExactCategory C] in
/-- The actual stabilizer matrix sends ((t1,t2),a) to ((t2-t1,a),t1). -/
def differencePermutationIso (T A : C) : (T ⊞ T) ⊞ A ≅ (T ⊞ A) ⊞ T where
  hom := biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.snd - biprod.fst ≫ biprod.fst) biprod.snd)
    (biprod.fst ≫ biprod.fst)
  inv := biprod.lift
    (biprod.lift biprod.snd (biprod.fst ≫ biprod.fst + biprod.snd))
    (biprod.fst ≫ biprod.snd)
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp [Category.assoc, comp_add]
    · simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp [Category.assoc, comp_sub]
    · simp [Category.assoc]

/-- The original raw row map supplies the kernel Iso in the stabilizer comparison. -/
def diagonalStabilizerIso {a b : Auxiliary C X} (r : RawHom a b) :
    (r.stabilizer ⊗ r.stabilizer) ⊗ (⟨a.of.A⟩ : Core C) ≅
      (⟨b.of.A⟩ : Core C) ⊗ r.stabilizer :=
  Core.isoMk (differencePermutationIso r.stabilizer.of a.of.A ≪≫
    biprod.mapIso r.hom.a (Iso.refl r.stabilizer.of))

@[simp]
theorem diagonalStabilizerIso_hom {a b : Auxiliary C X} (r : RawHom a b) :
    (diagonalStabilizerIso r).hom.iso.hom =
      (differencePermutationIso r.stabilizer.of a.of.A).hom ≫
        biprod.map r.hom.a.hom (𝟙 r.stabilizer.of) := rfl

private theorem auxComp_middle {a b c : Auxiliary C X}
    (r : RawHom a b) (s : RawHom b c) :
    (r.comp s).hom.b.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.B).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.b.hom ≫ s.hom.b.hom := rfl

omit [HasZeroObject C] [ExactCategory C] in
private theorem biprodKernelTransport_heq {A B Z D : C} (p : A = B) (f : A ⟶ Z) :
    HEq (biprod.map ((eqToIso p).inv ≫ f) (𝟙 D)) (biprod.map f (𝟙 D)) := by
  cases p
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]
  exact HEq.rfl

private theorem canonicalSelfObj_eq (E : FixedTargetExtension C X) :
    (convolutionPullback E E).obj = (selfPullback E).obj := by rfl

private def canonicalDiagonalMiddle (E : FixedTargetExtension C X) :
    E.A ⊞ E.B ⟶ (convolutionPullback E E).obj :=
  middleForward E ≫ (eqToIso (canonicalSelfObj_eq E)).inv

private theorem canonicalSelf_inv_fst (E : FixedTargetExtension C X) :
    (eqToIso (canonicalSelfObj_eq E)).inv ≫ (convolutionPullback E E).fst =
      (selfPullback E).fst := by
  have h := (conj_eqToHom_iff_heq (selfPullback E).fst (convolutionPullback E E).fst
    (canonicalSelfObj_eq E).symm (rfl : E.B = E.B)).2 (by rfl)
  simpa only [eqToIso.inv, eqToHom_refl, Category.comp_id] using h.symm

private theorem canonicalSelf_inv_snd (E : FixedTargetExtension C X) :
    (eqToIso (canonicalSelfObj_eq E)).inv ≫ (convolutionPullback E E).snd =
      (selfPullback E).snd := by
  have h := (conj_eqToHom_iff_heq (selfPullback E).snd (convolutionPullback E E).snd
    (canonicalSelfObj_eq E).symm (rfl : E.B = E.B)).2 (by rfl)
  simpa only [eqToIso.inv, eqToHom_refl, Category.comp_id] using h.symm

@[reassoc]
private theorem canonicalDiagonalMiddle_fst (E : FixedTargetExtension C X) :
    canonicalDiagonalMiddle E ≫ (convolutionPullback E E).fst =
      (biprod.snd : E.A ⊞ E.B ⟶ E.B) := by
  unfold canonicalDiagonalMiddle
  rw [Category.assoc, canonicalSelf_inv_fst]
  exact middleForward_fst E

@[reassoc]
private theorem canonicalDiagonalMiddle_snd (E : FixedTargetExtension C X) :
    canonicalDiagonalMiddle E ≫ (convolutionPullback E E).snd =
      (biprod.fst : E.A ⊞ E.B ⟶ E.A) ≫ E.i + biprod.snd := by
  unfold canonicalDiagonalMiddle
  rw [Category.assoc, canonicalSelf_inv_snd]
  exact middleForward_snd E

private theorem convolutionDiagonal_middle_heq (E : FixedTargetExtension C X) :
    HEq (convolutionDiagonalRaw E).hom.b.hom (canonicalDiagonalMiddle E) := by
  have hd := heq_of_eq (convolutionDiagonalRaw_middle E)
  have hc : HEq (canonicalDiagonalMiddle E) (middleForward E) := by
    simpa only [canonicalDiagonalMiddle, eqToIso.inv] using
      (comp_eqToHom_heq (middleForward E) (canonicalSelfObj_eq E).symm)
  exact hd.trans hc.symm

private theorem rawComp_row_middle {a b c : Auxiliary C X}
    (r : RawHom a b) (s : RawHom b c) :
    (r.comp s).hom.b.hom =
      (FixedTargetExtension.leftSumAssocIso s.stabilizer r.stabilizer a.of).hom.b.hom ≫
        (FixedTargetExtension.leftSumMap (𝟙 s.stabilizer) r.hom).b.hom ≫ s.hom.b.hom := by
  have hRow : (r.comp s).hom =
      (FixedTargetExtension.leftSumAssocIso s.stabilizer r.stabilizer a.of).hom ≫
        FixedTargetExtension.leftSumMap (𝟙 s.stabilizer) r.hom ≫ s.hom := by rfl
  have hb := congrArg
    (fun f : ((r.comp s).stabilizer ⊙ₗ a.of) ⟶ c.of => f.b.hom) hRow
  simpa only [FixedTargetExtension.comp_b, Iso.trans_hom] using hb

private theorem convolutionDiagonal_source_eq (E : FixedTargetExtension C X) :
    (((convolutionDiagonalRaw E).stabilizer ⊙ₗ E).B) = (E.A ⊞ E.B) := by rfl

private theorem rawNaturality_source_eq {a b : Auxiliary C X} (r : RawHom a b) :
    ((((convolutionDiagonalRaw a.of).comp (auxProductRaw r r)).stabilizer ⊙ₗ a.of).B) =
      (((r.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.A) ⊞ a.of.B) := by rfl

private theorem rawNaturality_product_obj_eq {a b : Auxiliary C X} (r : RawHom a b) :
    ((auxProductRaw r r).stabilizer.of) = (r.stabilizer.of ⊞ r.stabilizer.of) := by rfl

private theorem rawNaturality_left_mid1_eq {a b : Auxiliary C X} (r : RawHom a b) :
    ((FixedTargetExtension.leftSumObj (auxProductRaw r r).stabilizer
      ((convolutionDiagonalRaw a.of).stabilizer ⊙ₗ a.of)).B) =
        ((r.stabilizer.of ⊞ r.stabilizer.of) ⊞ (a.of.A ⊞ a.of.B)) := by rfl

private theorem rawNaturality_left_mid2_eq {a b : Auxiliary C X} (r : RawHom a b) :
    ((FixedTargetExtension.leftSumObj (auxProductRaw r r).stabilizer
      (convolutionObj a.of a.of)).B) =
        ((r.stabilizer.of ⊞ r.stabilizer.of) ⊞ (convolutionPullback a.of a.of).obj) := by rfl

private theorem rawNaturality_stab_left_eq {a b : Auxiliary C X} (r : RawHom a b) :
    (((r.stabilizer ⊗ r.stabilizer) ⊗ (⟨a.of.A⟩ : Core C)).of) =
      ((r.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.A) := by rfl

private theorem rawNaturality_stab_right_eq {a b : Auxiliary C X} (r : RawHom a b) :
    (((⟨b.of.A⟩ : Core C) ⊗ r.stabilizer).of) = (b.of.A ⊞ r.stabilizer.of) := by rfl

private theorem rawNaturality_right_mid1_eq {a b : Auxiliary C X} (r : RawHom a b) :
    (((r.comp (convolutionDiagonalRaw b.of)).stabilizer ⊙ₗ a.of).B) =
      ((b.of.A ⊞ r.stabilizer.of) ⊞ a.of.B) := by rfl

private theorem rawNaturality_right_mid2_eq {a b : Auxiliary C X} (r : RawHom a b) :
    ((FixedTargetExtension.leftSumObj (convolutionDiagonalRaw b.of).stabilizer
      (r.stabilizer ⊙ₗ a.of)).B) = (b.of.A ⊞ (r.stabilizer.of ⊞ a.of.B)) := by rfl

private theorem rawNaturality_right_mid3_eq (b : Auxiliary C X) :
    (((convolutionDiagonalRaw b.of).stabilizer ⊙ₗ b.of).B) = (b.of.A ⊞ b.of.B) := by rfl

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
private theorem rawMiddle_transport_eq_of_heq {A A' B B' : C}
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) :
    (eqToIso hA).inv ≫ f ≫ (eqToIso hB).hom = g := by
  cases hA
  cases hB
  simpa only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using (eq_of_heq h)

/-- The auxiliary diagonal is natural for every original stabilized raw map, without a section. -/
theorem diagonalRaw_naturality {a b : Auxiliary C X} (r : RawHom a b) :
    ((convolutionDiagonalRaw a.of).comp (auxProductRaw r r)).Rel
      (r.comp (convolutionDiagonalRaw b.of)) := by
  let E := a.of
  let F := b.of
  let T := r.stabilizer
  let h : FixedTargetExtension.leftSumObj T E ⟶ F := r.hom
  let ha : T.of ⊞ E.A ⟶ F.A :=
    (eqToIso (by exact leftSumObj_kernel_eq T E)).inv ≫ h.a.hom
  let hb : T.of ⊞ E.B ⟶ F.B :=
    (eqToIso (by exact leftSumObj_middle_eq T E) :
      (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv ≫ h.b.hom
  let e := diagonalStabilizerIso r
  have heRaw : e.hom.iso.hom =
      (differencePermutationIso T.of E.A).hom ≫ biprod.map ha (𝟙 T.of) := by
    let dOld : ((T ⊗ T) ⊗ (⟨E.A⟩ : Core C)).of ⟶
        (FixedTargetExtension.leftSumObj T E).A ⊞ T.of :=
      (differencePermutationIso T.of E.A).hom
    let dn : ((T ⊗ T) ⊗ (⟨E.A⟩ : Core C)).of ⟶ (T.of ⊞ E.A) ⊞ T.of :=
      (differencePermutationIso T.of E.A).hom
    have hd : HEq dOld dn := by rfl
    have hm : HEq (biprod.map ha (𝟙 T.of)) (biprod.map h.a.hom (𝟙 T.of)) := by
      exact biprodKernelTransport_heq (leftSumObj_kernel_eq T E) h.a.hom
    have hc := heq_comp (rfl : (((T ⊗ T) ⊗ (⟨E.A⟩ : Core C)).of) =
        (((T ⊗ T) ⊗ (⟨E.A⟩ : Core C)).of))
      (congrArg (fun Y : C => Y ⊞ T.of) (leftSumObj_kernel_eq T E))
      (rfl : (F.A ⊞ T.of) = (F.A ⊞ T.of)) hd hm.symm
    have ho : HEq e.hom.iso.hom (dOld ≫ biprod.map h.a.hom (𝟙 T.of)) := by
      exact heq_of_eq (diagonalStabilizerIso_hom r)
    exact eq_of_heq (ho.trans hc)
  let W : C := ((T.of ⊞ T.of) ⊞ E.A) ⊞ E.B
  let t1 : W ⟶ T.of :=
    (biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫
      (biprod.fst : (T.of ⊞ T.of) ⊞ E.A ⟶ T.of ⊞ T.of) ≫
      (biprod.fst : T.of ⊞ T.of ⟶ T.of)
  let t2 : W ⟶ T.of :=
    (biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫
      (biprod.fst : (T.of ⊞ T.of) ⊞ E.A ⟶ T.of ⊞ T.of) ≫
      (biprod.snd : T.of ⊞ T.of ⟶ T.of)
  let aa : W ⟶ E.A :=
    (biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫
      (biprod.snd : (T.of ⊞ T.of) ⊞ E.A ⟶ E.A)
  let bb : W ⟶ E.B := (biprod.snd : W ⟶ E.B)
  let j1 : W ⟶ T.of ⊞ E.B := biprod.lift t1 bb
  let j2 : W ⟶ T.of ⊞ E.B := biprod.lift t2 (aa ≫ E.i + bb)
  let kk : W ⟶ T.of ⊞ E.A := biprod.lift (t2 - t1) aa
  let lc : W ⟶ (T.of ⊞ T.of) ⊞ (convolutionPullback E E).obj :=
    (biprod.associator (T.of ⊞ T.of) E.A E.B).hom ≫
      biprod.map (𝟙 (T.of ⊞ T.of)) (canonicalDiagonalMiddle E)
  let eNative : (T.of ⊞ T.of) ⊞ E.A ⟶ F.A ⊞ T.of :=
    (differencePermutationIso T.of E.A).hom ≫ biprod.map ha (𝟙 T.of)
  let rc : W ⟶ F.A ⊞ (T.of ⊞ E.B) :=
    biprod.map eNative (𝟙 E.B) ≫ (biprod.associator F.A T.of E.B).hom
  have hLcPair : lc ≫ (biprod.fst : (T.of ⊞ T.of) ⊞
      (convolutionPullback E E).obj ⟶ T.of ⊞ T.of) =
      (biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫ biprod.fst := by
    have h := congrArg
      (fun q : ((T.of ⊞ T.of) ⊞ (E.A ⊞ E.B)) ⟶ T.of ⊞ T.of =>
        (biprod.associator (T.of ⊞ T.of) E.A E.B).hom ≫ q)
      (biprod.map_fst (𝟙 (T.of ⊞ T.of)) (canonicalDiagonalMiddle E))
    simpa only [lc, Category.assoc, Category.comp_id, biprod.associator,
      biprod.lift_fst] using h
  have hLcFirst : lc ≫ biprod.snd ≫ (convolutionPullback E E).fst = bb := by
    have h := congrArg
      (fun q : E.A ⊞ E.B ⟶ E.B =>
        (biprod.associator (T.of ⊞ T.of) E.A E.B).hom ≫ biprod.snd ≫ q)
      (canonicalDiagonalMiddle_fst E)
    simpa only [lc, Category.assoc, biprod.map_snd_assoc, biprod.associator,
      biprod.lift_snd_assoc, biprod.lift_snd, bb] using h
  have hLcSecond : lc ≫ biprod.snd ≫ (convolutionPullback E E).snd =
      aa ≫ E.i + bb := by
    have h := congrArg
      (fun q : E.A ⊞ E.B ⟶ E.B =>
        (biprod.associator (T.of ⊞ T.of) E.A E.B).hom ≫ biprod.snd ≫ q)
      (canonicalDiagonalMiddle_snd E)
    simpa only [lc, aa, bb, Category.assoc, biprod.map_snd_assoc, biprod.associator,
      comp_add, biprod.lift_snd_assoc, biprod.lift_snd, biprod.lift_fst,
      biprod.lift_fst_assoc] using h
  have hl1 : lc ≫ actionConvolutionFirst T T E E = j1 := by
    apply biprod.hom_ext
    · have h := congrArg (fun q : W ⟶ T.of ⊞ T.of => q ≫ biprod.fst) hLcPair
      simpa only [Category.assoc, actionConvolutionFirst,
        biprod.lift_fst_assoc, biprod.lift_fst, j1, t1] using h
    · simpa only [Category.assoc, actionConvolutionFirst,
        biprod.lift_snd_assoc, biprod.lift_snd, j1] using hLcFirst
  have hl2 : lc ≫ actionConvolutionSecond T T E E = j2 := by
    apply biprod.hom_ext
    · have h := congrArg (fun q : W ⟶ T.of ⊞ T.of => q ≫ biprod.snd) hLcPair
      simpa only [Category.assoc, actionConvolutionSecond,
        biprod.lift_fst_assoc, biprod.lift_fst, j2, t2] using h
    · simpa only [Category.assoc, actionConvolutionSecond,
        biprod.lift_snd_assoc, biprod.lift_snd, j2] using hLcSecond
  have hkv : (biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫
        (differencePermutationIso T.of E.A).hom ≫
        (biprod.fst : (T.of ⊞ E.A) ⊞ T.of ⟶ T.of ⊞ E.A) = kk := by
    apply biprod.hom_ext <;>
      simp [differencePermutationIso, kk, t1, t2, aa, Category.assoc]
  have hr0 : rc ≫ (biprod.fst : F.A ⊞ (T.of ⊞ E.B) ⟶ F.A) = kk ≫ ha := by
    calc
      _ = ((biprod.fst : W ⟶ (T.of ⊞ T.of) ⊞ E.A) ≫
          (differencePermutationIso T.of E.A).hom ≫
          (biprod.fst : (T.of ⊞ E.A) ⊞ T.of ⟶ T.of ⊞ E.A)) ≫ ha := by
        simp [rc, eNative, Category.assoc, biprod.associator]
      _ = _ := congrArg (· ≫ ha) hkv
  have hr1 : rc ≫ (biprod.snd : F.A ⊞ (T.of ⊞ E.B) ⟶ T.of ⊞ E.B) = j1 := by
    apply biprod.hom_ext <;>
      simp [rc, eNative, differencePermutationIso, j1, t1, bb,
        biprod.associator, Category.assoc]
  have hsum : kk ≫ biprod.map (𝟙 T.of) E.i + j1 = j2 := by
    apply biprod.hom_ext <;>
      simp [kk, j1, j2, Category.assoc, add_comp]
  have hi : biprod.map (𝟙 T.of) E.i ≫ hb = ha ≫ F.i := by
    have hSource :
        (eqToIso (by exact leftSumObj_kernel_eq T E)).inv ≫
          (FixedTargetExtension.leftSumObj T E).i =
        biprod.map (𝟙 T.of) E.i ≫
          (eqToIso (by exact leftSumObj_middle_eq T E) :
            (FixedTargetExtension.leftSumObj T E).B ≅ (T.of ⊞ E.B)).inv := by
      exact leftSumObj_i_pre_kernel T E
    dsimp only [ha, hb]
    rw [← Category.assoc, ← hSource, Category.assoc, h.comm_i]
    exact (Category.assoc _ _ _).symm
  have hMapFirst : actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h ≫
      (convolutionPullback F F).fst = actionConvolutionFirst T T E E ≫ hb := by
    simp only [convolutionMiddleMap_fst, actionConvolutionMiddle_first_assoc, hb]
  have hMapSecond : actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h ≫
      (convolutionPullback F F).snd = actionConvolutionSecond T T E E ≫ hb := by
    simp only [convolutionMiddleMap_snd, actionConvolutionMiddle_second_assoc, hb]
  have hFirstF : canonicalDiagonalMiddle F ≫ (convolutionPullback F F).fst =
      (biprod.snd : F.A ⊞ F.B ⟶ F.B) := canonicalDiagonalMiddle_fst F
  have hSecondF : canonicalDiagonalMiddle F ≫ (convolutionPullback F F).snd =
      (biprod.fst : F.A ⊞ F.B ⟶ F.A) ≫ F.i + biprod.snd := canonicalDiagonalMiddle_snd F
  have hMiddle :
      (lc ≫ actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h :
        W ⟶ (convolutionPullback F F).obj) =
      (rc ≫ biprod.map (𝟙 F.A) hb ≫ canonicalDiagonalMiddle F :
        W ⟶ (convolutionPullback F F).obj) := by
    apply (convolutionPullback F F).square.hom_ext
    · have hl : (lc ≫ actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h) ≫
          (convolutionPullback F F).fst = j1 ≫ hb := by
        simp only [Category.assoc, hMapFirst]
        exact (Category.assoc lc (actionConvolutionFirst T T E E) hb).symm.trans
          (congrArg (fun q : W ⟶ T.of ⊞ E.B => q ≫ hb) hl1)
      have hr : (rc ≫ biprod.map (𝟙 F.A) hb ≫ canonicalDiagonalMiddle F) ≫
          (convolutionPullback F F).fst = j1 ≫ hb := by
        simp only [Category.assoc, hFirstF, biprod.map_snd]
        exact (Category.assoc rc (biprod.snd : F.A ⊞ (T.of ⊞ E.B) ⟶ T.of ⊞ E.B)
          hb).symm.trans
            (congrArg (fun q : W ⟶ T.of ⊞ E.B => q ≫ hb) hr1)
      exact hl.trans hr.symm
    · have hl : (lc ≫ actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h) ≫
          (convolutionPullback F F).snd = j2 ≫ hb := by
        simp only [Category.assoc, hMapSecond]
        exact (Category.assoc lc (actionConvolutionSecond T T E E) hb).symm.trans
          (congrArg (fun q : W ⟶ T.of ⊞ E.B => q ≫ hb) hl2)
      have hr : (rc ≫ biprod.map (𝟙 F.A) hb ≫ canonicalDiagonalMiddle F) ≫
          (convolutionPullback F F).snd = j2 ≫ hb := by
        simp only [Category.assoc, hSecondF]
        calc
          _ = (rc ≫ (biprod.fst : F.A ⊞ (T.of ⊞ E.B) ⟶ F.A)) ≫ F.i +
              (rc ≫ (biprod.snd : F.A ⊞ (T.of ⊞ E.B) ⟶ T.of ⊞ E.B)) ≫ hb := by
            simp only [comp_add, Category.assoc, biprod.map_fst_assoc,
              biprod.map_snd, Category.id_comp]
          _ = (kk ≫ ha) ≫ F.i + j1 ≫ hb := by rw [hr0, hr1]
          _ = (kk ≫ biprod.map (𝟙 T.of) E.i + j1) ≫ hb := by
            rw [Category.assoc, ← hi, add_comp, Category.assoc]
          _ = _ := congrArg (fun q : W ⟶ T.of ⊞ E.B => q ≫ hb) hsum
      exact hl.trans hr.symm
  let S := ((convolutionDiagonalRaw E).comp (auxProductRaw r r)).stabilizer ⊙ₗ E
  let Y := convolutionObj F F
  let L : S ⟶ Y := ((convolutionDiagonalRaw E).comp (auxProductRaw r r)).hom
  let R : S ⟶ Y := e.hom ⊵ₗ E ≫ (r.comp (convolutionDiagonalRaw F)).hom
  have sourceEq :
      (((convolutionDiagonalRaw E).comp (auxProductRaw r r)).stabilizer ⊙ₗ E).B = W :=
    rawNaturality_source_eq r
  let sourceIso := eqToIso sourceEq
  have hRawL : sourceIso.inv ≫ L.b.hom ≫ (convolutionObjMiddleIso F F).hom =
      lc ≫ actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h := by
    let d := convolutionDiagonalRaw E
    let s := auxProductRaw r r
    let aOld := (FixedTargetExtension.leftSumAssocIso s.stabilizer d.stabilizer E).hom.b.hom
    let bOld := (FixedTargetExtension.leftSumMap (𝟙 s.stabilizer) d.hom).b.hom
    let cOld := s.hom.b.hom
    let aNew := (biprod.associator (T.of ⊞ T.of) E.A E.B).hom
    let bNew := biprod.map (𝟙 (T.of ⊞ T.of)) (canonicalDiagonalMiddle E)
    let cNew := actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h
    have haMap : HEq aOld aNew := by
      exact (heq_of_eq (FixedTargetExtension.leftSumAssocIso_b_hom
        s.stabilizer d.stabilizer E)).trans (by rfl)
    have hbMap : HEq bOld bNew := by
      let idOld : s.stabilizer.of ⟶ s.stabilizer.of :=
        (𝟙 s.stabilizer : s.stabilizer ⟶ s.stabilizer).iso.hom
      let idNew : (T.of ⊞ T.of) ⟶ (T.of ⊞ T.of) := 𝟙 (T.of ⊞ T.of)
      have hId : HEq idOld idNew := by rfl
      have hk := biprod_map_heq (rawNaturality_product_obj_eq r)
        (rawNaturality_product_obj_eq r) (convolutionDiagonal_source_eq E)
        (convolutionObj_middle_eq E E) (f := idOld) (f' := idNew) hId
        (convolutionDiagonal_middle_heq E)
      exact (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
        (𝟙 s.stabilizer) d.hom)).trans hk
    have hcMap : HEq cOld cNew := heq_of_eq (auxProductRaw_middle r r)
    have hbc := heq_comp (rawNaturality_left_mid1_eq r)
      (rawNaturality_left_mid2_eq r) (convolutionObj_middle_eq F F) hbMap hcMap
    have habc := heq_comp (rawNaturality_source_eq r)
      (rawNaturality_left_mid1_eq r) (convolutionObj_middle_eq F F) haMap hbc
    have hOld : HEq L.b.hom (aOld ≫ bOld ≫ cOld) := by
      exact heq_of_eq (rawComp_row_middle d s)
    have hNew : aNew ≫ bNew ≫ cNew =
        lc ≫ actionConvolutionMiddle T T E E ≫ convolutionMiddleMap h h := by
      simp only [aNew, bNew, cNew, lc, Category.assoc]
    have hField := hOld.trans (habc.trans (heq_of_eq hNew))
    have hCast := rawMiddle_transport_eq_of_heq sourceEq
      (convolutionObj_middle_eq F F) hField
    simpa only [sourceIso, convolutionObjMiddleIso] using hCast
  have hRawR : sourceIso.inv ≫ R.b.hom ≫ (convolutionObjMiddleIso F F).hom =
      rc ≫ biprod.map (𝟙 F.A) hb ≫ canonicalDiagonalMiddle F := by
    let d := convolutionDiagonalRaw F
    let aOld := (FixedTargetExtension.leftSumMap e.hom (𝟙 E)).b.hom
    let bOld := (FixedTargetExtension.leftSumAssocIso d.stabilizer r.stabilizer E).hom.b.hom
    let cOld := (FixedTargetExtension.leftSumMap (𝟙 d.stabilizer) r.hom).b.hom
    let dOld := d.hom.b.hom
    let aNew := biprod.map eNative (𝟙 E.B)
    let bNew := (biprod.associator F.A T.of E.B).hom
    let cNew := biprod.map (𝟙 F.A) hb
    let dNew := canonicalDiagonalMiddle F
    have haMap : HEq aOld aNew := by
      let idOld : E.B ⟶ E.B := (𝟙 E : E ⟶ E).b.hom
      let idNew : E.B ⟶ E.B := 𝟙 E.B
      have hIdEq : (𝟙 E : E ⟶ E).b.hom = 𝟙 E.B := by
        simp only [FixedTargetExtension.id_b, Iso.refl_hom]
      have hId : HEq idOld idNew := heq_of_eq hIdEq
      have hk := biprod_map_heq (rawNaturality_stab_left_eq r)
        (rawNaturality_stab_right_eq r) (rfl : E.B = E.B) (rfl : E.B = E.B)
        (g := idOld) (g' := idNew) (heq_of_eq heRaw) hId
      exact (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom e.hom (𝟙 E))).trans hk
    have hbMap : HEq bOld bNew := by
      exact (heq_of_eq (FixedTargetExtension.leftSumAssocIso_b_hom
        d.stabilizer r.stabilizer E)).trans (by rfl)
    have hh : HEq h.b.hom hb := by
      have hx : HEq hb h.b.hom := by
        simpa only [hb, eqToIso.inv] using
          (eqToHom_comp_heq h.b.hom (leftSumObj_middle_eq T E).symm)
      exact hx.symm
    have hcMap : HEq cOld cNew := by
      let idOld : d.stabilizer.of ⟶ d.stabilizer.of :=
        (𝟙 d.stabilizer : d.stabilizer ⟶ d.stabilizer).iso.hom
      let idNew : F.A ⟶ F.A := 𝟙 F.A
      have hId : HEq idOld idNew := by rfl
      have hk := biprod_map_heq (rfl : d.stabilizer.of = F.A)
        (rfl : d.stabilizer.of = F.A) (leftSumObj_middle_eq T E)
        (rfl : F.B = F.B) (f := idOld) (f' := idNew) hId hh
      exact (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
        (𝟙 d.stabilizer) r.hom)).trans hk
    have hdMap : HEq dOld dNew := convolutionDiagonal_middle_heq F
    have hcd := heq_comp (rawNaturality_right_mid2_eq r)
      (rawNaturality_right_mid3_eq b) (convolutionObj_middle_eq F F) hcMap hdMap
    have hbcd := heq_comp (rawNaturality_right_mid1_eq r)
      (rawNaturality_right_mid2_eq r) (convolutionObj_middle_eq F F) hbMap hcd
    have habcd := heq_comp (rawNaturality_source_eq r)
      (rawNaturality_right_mid1_eq r) (convolutionObj_middle_eq F F) haMap hbcd
    have hOld : HEq R.b.hom (aOld ≫ bOld ≫ cOld ≫ dOld) := by
      let S0 : Core C := (r.stabilizer ⊗ r.stabilizer) ⊗ (⟨E.A⟩ : Core C)
      let S1 : Core C := (⟨F.A⟩ : Core C) ⊗ r.stabilizer
      have hSource : (S0 ⊙ₗ E).B = (FixedTargetExtension.leftSumObj S0 E).B := rfl
      have hMiddle : (S1 ⊙ₗ E).B = (FixedTargetExtension.leftSumObj S1 E).B := rfl
      have hAction : HEq (e.hom ⊵ₗ E).b.hom aOld := by rfl
      have hInner : HEq (r.comp d).hom.b.hom (bOld ≫ cOld ≫ dOld) :=
        heq_of_eq (rawComp_row_middle r d)
      have hComp := heq_comp hSource hMiddle
        (rfl : (convolutionObj F F).B = (convolutionObj F F).B) hAction hInner
      have hRow := congrArg Iso.hom (FixedTargetExtension.comp_b
        (e.hom ⊵ₗ E) (r.comp d).hom)
      exact (heq_of_eq hRow).trans hComp
    have hNew : aNew ≫ bNew ≫ cNew ≫ dNew =
        rc ≫ biprod.map (𝟙 F.A) hb ≫ canonicalDiagonalMiddle F := by
      simp only [aNew, bNew, cNew, dNew, rc, Category.assoc]
    have hField := hOld.trans (habcd.trans (heq_of_eq hNew))
    have hCast := rawMiddle_transport_eq_of_heq sourceEq
      (convolutionObj_middle_eq F F) hField
    simpa only [sourceIso, convolutionObjMiddleIso] using hCast
  refine ⟨e, ?_⟩
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  have hc := hRawR.trans (hMiddle.symm.trans hRawL.symm)
  have hRow : R.b.hom = L.b.hom := by
    apply (cancel_epi sourceIso.inv).mp
    apply (cancel_mono (convolutionObjMiddleIso F F).hom).mp
    simp only [Category.assoc] at hc ⊢
    exact hc
  exact hRow

/-- Doubling uses the actual auxiliary product functor on the same L. -/
def auxiliaryDoubling : Auxiliary C X ⥤ Auxiliary C X :=
  (𝟭 (Auxiliary C X)).prod' (𝟭 (Auxiliary C X)) ⋙ auxiliaryProduct

/-- The actual IV.7.6 auxiliary diagonal natural transformation. -/
def auxiliaryDiagonal : 𝟭 (Auxiliary C X) ⟶ auxiliaryDoubling where
  app a := MonoidalActionCategory.Hom.mk (convolutionDiagonalRaw a.of)
  naturality {a b} f := by
    obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
    exact (_root_.Quotient.sound (diagonalRaw_naturality r)).symm

/-- The component retains the original kernel as its actual stabilizer. -/
theorem auxiliaryDiagonal_app (a : Auxiliary C X) :
    auxiliaryDiagonal.app a = MonoidalActionCategory.Hom.mk (convolutionDiagonalRaw a.of) := rfl

end AlgebraicKTheory.AuxiliaryExtension

end


noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

private theorem raw_post_map {a b : Auxiliary C X} (r : RawHom a b)
    {F : FixedTargetExtension C X} (f : b.of ⟶ F) :
    (r.comp (RawHom.ofMap (S := Core C) f)).Rel
      (⟨r.stabilizer, r.hom ≫ f⟩ : RawHom a ⟨F⟩) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  dsimp only [RawHom.comp, RawHom.ofMap]
  rw [MonoidalLeftAction.leftUnitor_actionHom]
  simp only [Category.assoc]
  simp only [Category.assoc, MonoidalLeftAction.actionHomRight_comp,
    MonoidalLeftAction.actionUnitIso_hom_naturality]

private theorem raw_pre_map {a b : Auxiliary C X} (r : RawHom a b)
    {E : FixedTargetExtension C X} (f : E ⟶ a.of) :
    ((RawHom.ofMap (S := Core C) f).comp r).Rel
      (⟨r.stabilizer, FixedTargetExtension.leftSumMap (𝟙 r.stabilizer) f ≫ r.hom⟩ :
        RawHom ⟨E⟩ b) := by
  refine ⟨ρ_ r.stabilizer, ?_⟩
  dsimp only [RawHom.comp, RawHom.ofMap]
  rw [MonoidalLeftAction.rightUnitor_actionHom,
    MonoidalLeftAction.actionHomRight_comp]
  have hmap : r.stabilizer ⊴ₗ f = FixedTargetExtension.leftSumMap (𝟙 r.stabilizer) f := rfl
  simp only [Category.assoc, hmap]

/-- The actual left action/convolution unit comparison, before any quotient or realization. -/
private theorem actionLeftUnit_canonical (T : Core C) (E : FixedTargetExtension C X) :
    (actionConvolutionMiddle (𝟙_ (Core C)) T (unitRow X) E ≫
      convolutionMiddleMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom
        (𝟙 (FixedTargetExtension.leftSumObj T E)) ≫
      (convolutionPullback (unitRow X) (FixedTargetExtension.leftSumObj T E)).snd) ≫
      (eqToIso (leftSumObj_middle_eq T E)).hom =
    biprod.map (biprod.snd : (0 : C) ⊞ T.of ⟶ T.of)
      (𝟙 (convolutionPullback (unitRow X) E).obj) ≫
      biprod.map (𝟙 T.of) (convolutionPullback (unitRow X) E).snd := by
  simp only [Category.assoc, convolutionMiddleMap_snd_assoc, FixedTargetExtension.id_b,
    Iso.refl_hom]
  apply biprod.hom_ext <;> simp [actionConvolutionSecond, Category.assoc]

private theorem actionRightUnit_canonical (T : Core C) (E : FixedTargetExtension C X) :
    (actionConvolutionMiddle T (𝟙_ (Core C)) E (unitRow X) ≫
      convolutionMiddleMap (𝟙 (FixedTargetExtension.leftSumObj T E))
        (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
      (convolutionPullback (FixedTargetExtension.leftSumObj T E) (unitRow X)).fst) ≫
      (eqToIso (leftSumObj_middle_eq T E)).hom =
    biprod.map (biprod.fst : T.of ⊞ (0 : C) ⟶ T.of)
      (𝟙 (convolutionPullback E (unitRow X)).obj) ≫
      biprod.map (𝟙 T.of) (convolutionPullback E (unitRow X)).fst := by
  simp only [Category.assoc, convolutionMiddleMap_fst_assoc, FixedTargetExtension.id_b,
    Iso.refl_hom]
  apply biprod.hom_ext <;> simp [actionConvolutionFirst, Category.assoc]

theorem actionConvolution_left_unit (T : Core C) (E : FixedTargetExtension C X) :
    (actionConvolutionIso (𝟙_ (Core C)) T (unitRow X) E).hom ≫
        convolutionMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom
          (𝟙 (FixedTargetExtension.leftSumObj T E)) ≫
        (convolutionLeftUnitIso (FixedTargetExtension.leftSumObj T E)).hom =
      FixedTargetExtension.leftSumMap (λ_ T).hom (𝟙 (convolutionObj (unitRow X) E)) ≫
        FixedTargetExtension.leftSumMap (𝟙 T) (convolutionLeftUnitIso E).hom := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  let I := unitRow X
  let Q := convolutionObj I E
  let P := convolutionPullback I E
  let Z := FixedTargetExtension.leftSumObj T E
  let A1 := (actionConvolutionIso (𝟙_ (Core C)) T I E).hom
  let A2 := convolutionMap (FixedTargetExtension.leftSumUnitIso I).hom (𝟙 Z)
  let A3 := (convolutionLeftUnitIso Z).hom
  let B1 := FixedTargetExtension.leftSumMap (λ_ T).hom (𝟙 Q)
  let B2 := FixedTargetExtension.leftSumMap (𝟙 T) (convolutionLeftUnitIso E).hom
  let l := A1 ≫ A2 ≫ A3
  let r := B1 ≫ B2
  let lc := actionConvolutionMiddle (𝟙_ (Core C)) T I E ≫
    convolutionMiddleMap (FixedTargetExtension.leftSumUnitIso I).hom (𝟙 Z) ≫
      (convolutionPullback I Z).snd
  let rc := biprod.map (biprod.snd : (0 : C) ⊞ T.of ⟶ T.of) (𝟙 P.obj) ≫
    biprod.map (𝟙 T.of) P.snd
  have hP : Q.B = P.obj := convolutionObj_middle_eq I E
  have hM : (FixedTargetExtension.leftSumObj T Q).B = (T.of ⊞ P.obj) := rfl
  have hZ : Z.B = (T.of ⊞ E.B) := leftSumObj_middle_eq T E
  have hl : HEq l.b.hom lc := by
    have hS := leftSumTensor_middle_eq (𝟙_ (Core C)) T I E
    have h1 := convolutionObj_middle_eq (FixedTargetExtension.leftSumObj (𝟙_ (Core C)) I) Z
    have h2 := convolutionObj_middle_eq I Z
    have hA1 := heq_of_eq (actionConvolutionIso_middle (𝟙_ (Core C)) T I E)
    have hA2 := heq_of_eq (convolutionMap_middle (FixedTargetExtension.leftSumUnitIso I).hom (𝟙 Z))
    have hA3 := heq_of_eq (convolutionLeftUnitIso_middle Z)
    have h23 := heq_comp h1 h2 (rfl : Z.B = Z.B) hA2 hA3
    have h123 := heq_comp hS h1 (rfl : Z.B = Z.B) hA1 h23
    have hRow : l.b.hom = A1.b.hom ≫ A2.b.hom ≫ A3.b.hom := by
      simp only [l, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h123
  have hp : HEq (lc ≫ (eqToIso (leftSumObj_middle_eq T E)).hom) lc := by
    simpa only [eqToIso.hom] using (comp_eqToHom_heq lc (leftSumObj_middle_eq T E))
  have hr : HEq r.b.hom rc := by
    have hCore : ((𝟙_ (Core C)) ⊗ T).of = ((0 : C) ⊞ T.of) := rfl
    have hS : (FixedTargetExtension.leftSumObj ((𝟙_ (Core C)) ⊗ T) Q).B =
        (((0 : C) ⊞ T.of) ⊞ P.obj) := rfl
    have hUnitor : ((λ_ T).hom : (𝟙_ (Core C)) ⊗ T ⟶ T).iso.hom =
        (biprod.snd : (0 : C) ⊞ T.of ⟶ T.of) := rfl
    have hIdOld : (𝟙 Q : Q ⟶ Q).b.hom = 𝟙 Q.B := by
      simp only [FixedTargetExtension.id_b, Iso.refl_hom]
    have hId := (heq_of_eq hIdOld).trans
      ((eqToHom_heq_id_dom Q.B P.obj hP).symm.trans
        (eqToHom_heq_id_cod Q.B P.obj hP))
    have hMap1 := biprod_map_heq hCore (rfl : T.of = T.of) hP hP
      (heq_of_eq hUnitor) hId
    have hB1 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
      (λ_ T).hom (𝟙 Q))).trans hMap1
    have hCoreId : (𝟙 T : T ⟶ T).iso.hom = 𝟙 T.of := rfl
    have hMap2 := biprod_map_heq (rfl : T.of = T.of) (rfl : T.of = T.of)
      hP (rfl : E.B = E.B) (heq_of_eq hCoreId)
      (heq_of_eq (convolutionLeftUnitIso_middle E))
    have hB2 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom (𝟙 T)
      (convolutionLeftUnitIso E).hom)).trans hMap2
    have h12 := heq_comp hS hM hZ hB1 hB2
    have hRow : r.b.hom = B1.b.hom ≫ B2.b.hom := by
      simp only [r, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h12
  exact eq_of_heq (hl.trans (hp.symm.trans
    ((heq_of_eq (actionLeftUnit_canonical T E)).trans hr.symm)))

/-- The actual right action/convolution unit comparison keeps the original stabilizer. -/
theorem actionConvolution_right_unit (T : Core C) (E : FixedTargetExtension C X) :
    (actionConvolutionIso T (𝟙_ (Core C)) E (unitRow X)).hom ≫
        convolutionMap (𝟙 (FixedTargetExtension.leftSumObj T E))
          (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
        (convolutionRightUnitIso (FixedTargetExtension.leftSumObj T E)).hom =
      FixedTargetExtension.leftSumMap (ρ_ T).hom (𝟙 (convolutionObj E (unitRow X))) ≫
        FixedTargetExtension.leftSumMap (𝟙 T) (convolutionRightUnitIso E).hom := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  let I := unitRow X
  let Q := convolutionObj E I
  let P := convolutionPullback E I
  let Z := FixedTargetExtension.leftSumObj T E
  let A1 := (actionConvolutionIso T (𝟙_ (Core C)) E I).hom
  let A2 := convolutionMap (𝟙 Z) (FixedTargetExtension.leftSumUnitIso I).hom
  let A3 := (convolutionRightUnitIso Z).hom
  let B1 := FixedTargetExtension.leftSumMap (ρ_ T).hom (𝟙 Q)
  let B2 := FixedTargetExtension.leftSumMap (𝟙 T) (convolutionRightUnitIso E).hom
  let l := A1 ≫ A2 ≫ A3
  let r := B1 ≫ B2
  let lc := actionConvolutionMiddle T (𝟙_ (Core C)) E I ≫
    convolutionMiddleMap (𝟙 Z) (FixedTargetExtension.leftSumUnitIso I).hom ≫
      (convolutionPullback Z I).fst
  let rc := biprod.map (biprod.fst : T.of ⊞ (0 : C) ⟶ T.of) (𝟙 P.obj) ≫
    biprod.map (𝟙 T.of) P.fst
  have hP : Q.B = P.obj := convolutionObj_middle_eq E I
  have hM : (FixedTargetExtension.leftSumObj T Q).B = (T.of ⊞ P.obj) := rfl
  have hZ : Z.B = (T.of ⊞ E.B) := leftSumObj_middle_eq T E
  have hl : HEq l.b.hom lc := by
    have hS := leftSumTensor_middle_eq T (𝟙_ (Core C)) E I
    have h1 := convolutionObj_middle_eq Z (FixedTargetExtension.leftSumObj (𝟙_ (Core C)) I)
    have h2 := convolutionObj_middle_eq Z I
    have hA1 := heq_of_eq (actionConvolutionIso_middle T (𝟙_ (Core C)) E I)
    have hA2 := heq_of_eq (convolutionMap_middle (𝟙 Z) (FixedTargetExtension.leftSumUnitIso I).hom)
    have hA3 := heq_of_eq (convolutionRightUnitIso_middle Z)
    have h23 := heq_comp h1 h2 (rfl : Z.B = Z.B) hA2 hA3
    have h123 := heq_comp hS h1 (rfl : Z.B = Z.B) hA1 h23
    have hRow : l.b.hom = A1.b.hom ≫ A2.b.hom ≫ A3.b.hom := by
      simp only [l, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h123
  have hp : HEq (lc ≫ (eqToIso (leftSumObj_middle_eq T E)).hom) lc := by
    simpa only [eqToIso.hom] using (comp_eqToHom_heq lc (leftSumObj_middle_eq T E))
  have hr : HEq r.b.hom rc := by
    have hCore : (T ⊗ (𝟙_ (Core C))).of = (T.of ⊞ (0 : C)) := rfl
    have hS : (FixedTargetExtension.leftSumObj (T ⊗ (𝟙_ (Core C))) Q).B =
        ((T.of ⊞ (0 : C)) ⊞ P.obj) := rfl
    have hUnitor : ((ρ_ T).hom : T ⊗ (𝟙_ (Core C)) ⟶ T).iso.hom =
        (biprod.fst : T.of ⊞ (0 : C) ⟶ T.of) := rfl
    have hIdOld : (𝟙 Q : Q ⟶ Q).b.hom = 𝟙 Q.B := by
      simp only [FixedTargetExtension.id_b, Iso.refl_hom]
    have hId := (heq_of_eq hIdOld).trans
      ((eqToHom_heq_id_dom Q.B P.obj hP).symm.trans
        (eqToHom_heq_id_cod Q.B P.obj hP))
    have hMap1 := biprod_map_heq hCore (rfl : T.of = T.of) hP hP
      (heq_of_eq hUnitor) hId
    have hB1 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom
      (ρ_ T).hom (𝟙 Q))).trans hMap1
    have hCoreId : (𝟙 T : T ⟶ T).iso.hom = 𝟙 T.of := rfl
    have hMap2 := biprod_map_heq (rfl : T.of = T.of) (rfl : T.of = T.of)
      hP (rfl : E.B = E.B) (heq_of_eq hCoreId)
      (heq_of_eq (convolutionRightUnitIso_middle E))
    have hB2 := (heq_of_eq (FixedTargetExtension.leftSumMap_b_hom (𝟙 T)
      (convolutionRightUnitIso E).hom)).trans hMap2
    have h12 := heq_comp hS hM hZ hB1 hB2
    have hRow : r.b.hom = B1.b.hom ≫ B2.b.hom := by
      simp only [r, FixedTargetExtension.comp_b, Iso.trans_hom]
    exact (heq_of_eq hRow).trans h12
  exact eq_of_heq (hl.trans (hp.symm.trans
    ((heq_of_eq (actionRightUnit_canonical T E)).trans hr.symm)))

private theorem left_unit_raw_natural {a b : Auxiliary C X} (r : RawHom a b) :
    (⟨(𝟙_ (Core C)) ⊗ r.stabilizer,
      (auxProductRaw (RawHom.id (auxiliaryUnit C X)) r).hom ≫
        (convolutionLeftUnitIso b.of).hom⟩ :
      RawHom ⟨convolutionObj (unitRow X) a.of⟩ b).Rel
      (⟨r.stabilizer, FixedTargetExtension.leftSumMap (𝟙 r.stabilizer)
        (convolutionLeftUnitIso a.of).hom ≫ r.hom⟩) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  dsimp only [auxiliaryUnit, RawHom.id, auxProductRaw]
  simp only [MonoidalLeftAction.actionHomLeft, MonoidalLeftAction.actionUnitIso, Category.assoc]
  change FixedTargetExtension.leftSumMap (λ_ r.stabilizer).hom
        (𝟙 (convolutionObj (unitRow X) a.of)) ≫
        (FixedTargetExtension.leftSumMap (𝟙 r.stabilizer)
          (convolutionLeftUnitIso a.of).hom ≫ r.hom) =
      (actionConvolutionIso (𝟙_ (Core C)) r.stabilizer (unitRow X) a.of).hom ≫
        convolutionMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom r.hom ≫
          (convolutionLeftUnitIso b.of).hom
  have hm : convolutionMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom r.hom =
      convolutionMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom
        (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of)) ≫
          convolutionMap (𝟙 (unitRow X)) r.hom := by
    simpa only [Category.comp_id, Category.id_comp] using
      (convolutionMap_comp (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom
        (𝟙 (unitRow X)) (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of)) r.hom)
  calc
    _ = ((actionConvolutionIso (𝟙_ (Core C)) r.stabilizer (unitRow X) a.of).hom ≫
        convolutionMap (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom
          (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of)) ≫
        (convolutionLeftUnitIso (FixedTargetExtension.leftSumObj r.stabilizer a.of)).hom) ≫
          r.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ r.hom) (actionConvolution_left_unit r.stabilizer a.of).symm)
    _ = _ := by
      rw [hm]
      simp only [Category.assoc, convolutionLeftUnitIso_natural]

private theorem right_unit_raw_natural {a b : Auxiliary C X} (r : RawHom a b) :
    (⟨r.stabilizer ⊗ (𝟙_ (Core C)),
      (auxProductRaw r (RawHom.id (auxiliaryUnit C X))).hom ≫
        (convolutionRightUnitIso b.of).hom⟩ :
      RawHom ⟨convolutionObj a.of (unitRow X)⟩ b).Rel
      (⟨r.stabilizer, FixedTargetExtension.leftSumMap (𝟙 r.stabilizer)
        (convolutionRightUnitIso a.of).hom ≫ r.hom⟩) := by
  refine ⟨ρ_ r.stabilizer, ?_⟩
  dsimp only [auxiliaryUnit, RawHom.id, auxProductRaw]
  simp only [MonoidalLeftAction.actionHomLeft, MonoidalLeftAction.actionUnitIso, Category.assoc]
  change FixedTargetExtension.leftSumMap (ρ_ r.stabilizer).hom
        (𝟙 (convolutionObj a.of (unitRow X))) ≫
        (FixedTargetExtension.leftSumMap (𝟙 r.stabilizer)
          (convolutionRightUnitIso a.of).hom ≫ r.hom) =
      (actionConvolutionIso r.stabilizer (𝟙_ (Core C)) a.of (unitRow X)).hom ≫
        convolutionMap r.hom (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
          (convolutionRightUnitIso b.of).hom
  have hm : convolutionMap r.hom (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom =
      convolutionMap (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of))
        (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
          convolutionMap r.hom (𝟙 (unitRow X)) := by
    simpa only [Category.comp_id, Category.id_comp] using
      (convolutionMap_comp (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of)) r.hom
        (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom (𝟙 (unitRow X)))
  calc
    _ = ((actionConvolutionIso r.stabilizer (𝟙_ (Core C)) a.of (unitRow X)).hom ≫
        convolutionMap (𝟙 (FixedTargetExtension.leftSumObj r.stabilizer a.of))
          (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
        (convolutionRightUnitIso (FixedTargetExtension.leftSumObj r.stabilizer a.of)).hom) ≫
          r.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ r.hom) (actionConvolution_right_unit r.stabilizer a.of).symm)
    _ = _ := by
      rw [hm]
      simp only [Category.assoc, convolutionRightUnitIso_natural]

/-- Left multiplication by the actual auxiliary unit. -/
def auxiliaryLeftUnitFunctor : Auxiliary C X ⥤ Auxiliary C X :=
  categoricalLeftUnitFunctor (Auxiliary C X) auxiliaryProduct (auxiliaryUnit C X)

/-- Right multiplication by the actual auxiliary unit. -/
def auxiliaryRightUnitFunctor : Auxiliary C X ⥤ Auxiliary C X :=
  categoricalRightUnitFunctor (Auxiliary C X) auxiliaryProduct (auxiliaryUnit C X)

/-- The left auxiliary unitor is the actual inclusion of the original row unitor. -/
def auxiliaryLeftUnitIso : auxiliaryLeftUnitFunctor (C := C) (X := X) ≅ 𝟭 (Auxiliary C X) :=
  NatIso.ofComponents
    (fun a => (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X)).mapIso
      (convolutionLeftUnitIso a.of)) (by
        intro a b f
        obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
        have hp := raw_post_map (auxProductRaw (RawHom.id (auxiliaryUnit C X)) r)
          (convolutionLeftUnitIso b.of).hom
        have hq := raw_pre_map r (convolutionLeftUnitIso a.of).hom
        exact (_root_.Quotient.sound hp).trans
          ((_root_.Quotient.sound (left_unit_raw_natural r)).trans
            (_root_.Quotient.sound hq).symm))

/-- The right auxiliary unitor preserves every original stabilizer and row map. -/
def auxiliaryRightUnitIso : auxiliaryRightUnitFunctor (C := C) (X := X) ≅ 𝟭 (Auxiliary C X) :=
  NatIso.ofComponents
    (fun a => (MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X)).mapIso
      (convolutionRightUnitIso a.of)) (by
        intro a b f
        obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
        have hp := raw_post_map (auxProductRaw r (RawHom.id (auxiliaryUnit C X)))
          (convolutionRightUnitIso b.of).hom
        have hq := raw_pre_map r (convolutionRightUnitIso a.of).hom
        exact (_root_.Quotient.sound hp).trans
          ((_root_.Quotient.sound (right_unit_raw_natural r)).trans
            (_root_.Quotient.sound hq).symm))

end AlgebraicKTheory.AuxiliaryExtension

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

/-- At the literal unit row the two actual auxiliary unitors have the same component. -/
theorem auxiliaryUnit_app_eq :
    auxiliaryLeftUnitIso.hom.app (auxiliaryUnit C X) =
      auxiliaryRightUnitIso.hom.app (auxiliaryUnit C X) := by
  have h : (convolutionLeftUnitIso (unitRow X)).hom =
      (convolutionRightUnitIso (unitRow X)).hom := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    let P := convolutionPullback (unitRow X) (unitRow X)
    change @Eq (P.obj ⟶ X) P.snd P.fst
    simpa only [unitRow, Category.comp_id] using P.square.w.symm
  exact congrArg
    ((MonoidalActionCategory.inclusion (Core C) (FixedTargetExtension C X)).map) h

private theorem diagonal_unit_row :
    (convolutionDiagonalRaw (unitRow X)).hom =
      (FixedTargetExtension.leftSumUnitIso (unitRow X)).hom ≫
        (convolutionLeftUnitIso (unitRow X)).inv := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  let I := unitRow X
  let g := (FixedTargetExtension.leftSumUnitIso I).hom ≫ (convolutionLeftUnitIso I).inv
  have hc : canonicalDiagonalMiddle I =
      (biprod.snd : (0 : C) ⊞ X ⟶ X) ≫ leftUnitMiddleInverse I := by
    apply (convolutionPullback I I).square.hom_ext
    · have hRight : ((biprod.snd : I.A ⊞ I.B ⟶ I.B) ≫ leftUnitMiddleInverse I) ≫
          (convolutionPullback I I).fst = (biprod.snd : I.A ⊞ I.B ⟶ I.B) := by
        change ((biprod.snd : I.A ⊞ I.B ⟶ I.B) ≫ leftUnitMiddleInverse I) ≫
          (convolutionPullback (unitRow X) I).fst = biprod.snd
        rw [Category.assoc, leftUnitMiddleInverse_fst]
        change (biprod.snd : I.A ⊞ I.B ⟶ I.B) ≫ (𝟙 I.B) = biprod.snd
        exact Category.comp_id _
      exact (canonicalDiagonalMiddle_fst I).trans hRight.symm
    · have hRight : ((biprod.snd : I.A ⊞ I.B ⟶ I.B) ≫ leftUnitMiddleInverse I) ≫
          (convolutionPullback I I).snd = (biprod.snd : I.A ⊞ I.B ⟶ I.B) := by
        change ((biprod.snd : I.A ⊞ I.B ⟶ I.B) ≫ leftUnitMiddleInverse I) ≫
          (convolutionPullback (unitRow X) I).snd = biprod.snd
        rw [Category.assoc, leftUnitMiddleInverse_snd, Category.comp_id]
      have hLeft : canonicalDiagonalMiddle I ≫ (convolutionPullback I I).snd =
          (biprod.snd : I.A ⊞ I.B ⟶ I.B) := by
        rw [canonicalDiagonalMiddle_snd]
        change (biprod.fst : (0 : C) ⊞ X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ X) +
          (biprod.snd : (0 : C) ⊞ X ⟶ X) = biprod.snd
        rw [comp_zero, zero_add]
      exact hLeft.trans hRight.symm
  have hInv : HEq (convolutionLeftUnitIso I).inv.b.hom (leftUnitMiddleInverse I) := by rfl
  have hg : HEq g.b.hom ((biprod.snd : (0 : C) ⊞ X ⟶ X) ≫ leftUnitMiddleInverse I) := by
    have hcomp := heq_comp (leftSumObj_middle_eq (𝟙_ (Core C)) I)
      (rfl : I.B = I.B) (convolutionObj_middle_eq I I)
      (heq_of_eq (FixedTargetExtension.leftSumUnitIso_b_hom I)) hInv
    simpa only [g, FixedTargetExtension.comp_b, Iso.trans_hom, I, unitRow] using hcomp
  exact eq_of_heq ((convolutionDiagonal_middle_heq I).trans
    ((heq_of_eq hc).trans hg.symm))

/-- At the actual unit the diagonal component is the inverse of the common unitor. -/
theorem auxiliaryDiagonal_unit_inv :
    auxiliaryDiagonal.app (auxiliaryUnit C X) =
      auxiliaryLeftUnitIso.inv.app (auxiliaryUnit C X) := by
  change MonoidalActionCategory.Hom.mk (convolutionDiagonalRaw (unitRow X)) =
    MonoidalActionCategory.Hom.mk
      (RawHom.ofMap (S := Core C) (convolutionLeftUnitIso (unitRow X)).inv)
  exact congrArg
    (fun k : FixedTargetExtension.leftSumObj (𝟙_ (Core C)) (unitRow X) ⟶
        convolutionObj (unitRow X) (unitRow X) =>
      MonoidalActionCategory.Hom.mk
        (⟨𝟙_ (Core C), k⟩ : RawHom (auxiliaryUnit C X)
          ⟨convolutionObj (unitRow X) (unitRow X)⟩)) diagonal_unit_row

/-- Native CGWH classifying space of the very same original auxiliary L. -/
def auxiliaryCGWH (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (X : C) :
    CGWH.{w, max u v} :=
  classifyingSpaceCGWH.{w, max u v, max u v}.obj (Cat.of (Auxiliary C X))

/-- The actual comparison with the original ordinary nerve realization. -/
def auxiliaryCGWHToTopIso :
    CGWH.cgwhToTop.obj (auxiliaryCGWH.{w} C X) ≅ auxiliarySpace C X :=
  classifyingSpaceCGWHToTopIso.{w, max u v, max u v}.app (Cat.of (Auxiliary C X))

/-- The original categorical product realizes to native multiplication. -/
def auxiliaryMulCGWH : auxiliaryCGWH.{w} C X ⨯ auxiliaryCGWH.{w} C X ⟶
    auxiliaryCGWH.{w} C X :=
  categoricalClassifyingSpaceMul.{w} (Auxiliary C X) auxiliaryProduct

/-- The selected point is the actual 0→X→X object, not a zero-fiber replacement. -/
def auxiliaryBasepointCGWH : auxiliaryCGWH.{w} C X :=
  classifyingSpaceCGWHPoint.{w} (auxiliaryUnit C X)

/-- The actual native weak-unit H-space data, including the common unitor root path. -/
def auxiliaryWeakHSpaceData : CGWH.WeakHSpaceData (auxiliaryCGWH.{w} C X) :=
  categoricalClassifyingSpaceWeakHSpaceData.{w}
    (Auxiliary C X) auxiliaryProduct (auxiliaryUnit C X)
    (by exact auxiliaryLeftUnitIso) (by exact auxiliaryRightUnitIso)
    (by exact auxiliaryUnit_app_eq)

theorem auxiliaryWeakHSpaceData_mul :
    (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).mul =
      auxiliaryMulCGWH.{w} (C := C) (X := X) := rfl

theorem auxiliaryWeakHSpaceData_e :
    (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).e =
      auxiliaryBasepointCGWH.{w} (C := C) (X := X) := rfl

/-- The native doubling map is the realization of the actual auxiliary doubling functor. -/
def auxiliaryDoublingCGWH : auxiliaryCGWH.{w} C X ⟶ auxiliaryCGWH.{w} C X :=
  classifyingSpaceCGWH.{w, max u v, max u v}.map auxiliaryDoubling.toCatHom

/-- The actual auxiliary diagonal realizes to Id~doubling on the same underlying space. -/
def auxiliaryDiagonalHomotopyCGWH :
    ContinuousMap.Homotopy (ContinuousMap.id (auxiliaryCGWH.{w} C X))
      (CGWH.cgwhToTop.map (auxiliaryDoublingCGWH.{w} (C := C) (X := X))).hom := by
  let H := classifyingSpaceCGWHNatTransHomotopy.{w}
    (auxiliaryDiagonal (C := C) (X := X))
  have hId : (CGWH.cgwhToTop.map
      (classifyingSpaceCGWH.{w, max u v, max u v}.map
        (𝟭 (Auxiliary C X)).toCatHom)).hom = ContinuousMap.id (auxiliaryCGWH.{w} C X) := by
    have hFunctor : (𝟭 (Auxiliary C X)).toCatHom = (𝟙 (Cat.of (Auxiliary C X))) := rfl
    rewrite [hFunctor, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  exact H.cast hId rfl

/-- The native categorical multiplication doubled on the diagonal is the actual doubling map. -/
theorem auxiliaryDoublingCGWH_eq_mul_diagonal :
    auxiliaryDoublingCGWH.{w} (C := C) (X := X) =
      Limits.prod.lift (𝟙 (auxiliaryCGWH.{w} C X)) (𝟙 (auxiliaryCGWH.{w} C X)) ≫
        auxiliaryMulCGWH.{w} (C := C) (X := X) := by
  let D := Auxiliary C X
  let B := classifyingSpaceCGWH.{w, max u v, max u v}
  let Δ : D ⥤ D × D := (𝟭 D).prod' (𝟭 D)
  let κ : B.obj (Cat.of (D × D)) ≅ B.obj (Cat.of D) ⨯ B.obj (Cat.of D) :=
    (SSet.toCGWH.mapIso (nerveProdIso D D)) ≪≫
      SSet.realizationProdIsoCGWH (nerve D) (nerve D)
  have hfst : κ.hom ≫ Limits.prod.fst = B.map (CategoryTheory.Prod.fst D D).toCatHom := by
    change (SSet.toCGWH.map (nerveProdIso D D).hom ≫
      (SSet.realizationProdIsoCGWH (nerve D) (nerve D)).hom) ≫ Limits.prod.fst = _
    rewrite [Category.assoc, SSet.realizationProdIsoCGWH_hom_fst,
      ← CategoryTheory.Functor.map_comp, nerveProdIso_hom_comp_fst]
    rfl
  have hsnd : κ.hom ≫ Limits.prod.snd = B.map (CategoryTheory.Prod.snd D D).toCatHom := by
    change (SSet.toCGWH.map (nerveProdIso D D).hom ≫
      (SSet.realizationProdIsoCGWH (nerve D) (nerve D)).hom) ≫ Limits.prod.snd = _
    rewrite [Category.assoc, SSet.realizationProdIsoCGWH_hom_snd,
      ← CategoryTheory.Functor.map_comp, nerveProdIso_hom_comp_snd]
    rfl
  have hΔ : B.map Δ.toCatHom ≫ κ.hom = Limits.prod.lift (𝟙 _) (𝟙 _) := by
    apply Limits.prod.hom_ext
    · rw [Category.assoc, hfst, ← B.map_comp, Limits.prod.lift_fst]
      change B.map (𝟙 (Cat.of D)) = 𝟙 (B.obj (Cat.of D))
      exact B.map_id _
    · rw [Category.assoc, hsnd, ← B.map_comp, Limits.prod.lift_snd]
      change B.map (𝟙 (Cat.of D)) = 𝟙 (B.obj (Cat.of D))
      exact B.map_id _
  have hΔ' : B.map Δ.toCatHom = Limits.prod.lift (𝟙 _) (𝟙 _) ≫ κ.inv := by
    calc
      B.map Δ.toCatHom = (B.map Δ.toCatHom ≫ κ.hom) ≫ κ.inv := by
        rw [Category.assoc, κ.hom_inv_id, Category.comp_id]
      _ = _ := congrArg (· ≫ κ.inv) hΔ
  change B.map (Δ.toCatHom ≫ auxiliaryProduct.toCatHom) = _
  rw [B.map_comp, hΔ']
  change (Limits.prod.lift (𝟙 _) (𝟙 _) ≫ κ.inv) ≫ B.map auxiliaryProduct.toCatHom =
    Limits.prod.lift (𝟙 _) (𝟙 _) ≫ (κ.inv ≫ B.map auxiliaryProduct.toCatHom)
  exact Category.assoc _ _ _

/-- Multiplication of the two selected points is the actual doubled-row vertex. -/
theorem auxiliaryMulCGWH_basepoint :
    auxiliaryMulCGWH.{w} (C := C) (X := X)
      (CGWH.prodPoint (auxiliaryCGWH.{w} C X) (auxiliaryCGWH.{w} C X)
        (auxiliaryBasepointCGWH.{w} (C := C) (X := X))
        (auxiliaryBasepointCGWH.{w} (C := C) (X := X))) =
      classifyingSpaceCGWHPoint.{w}
        (auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X)) :=
  categoricalClassifyingSpaceMul_prodPoint.{w}
    (Auxiliary C X) auxiliaryProduct (auxiliaryUnit C X) (auxiliaryUnit C X)

/-- The doubling map takes the selected point to the native multiplication point. -/
theorem auxiliaryDoublingCGWH_basepoint :
    auxiliaryDoublingCGWH.{w} (C := C) (X := X)
      (auxiliaryBasepointCGWH.{w} (C := C) (X := X)) =
      (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).mulUnit :=
  (classifyingSpaceCGWH_map_point.{w} auxiliaryDoubling (auxiliaryUnit C X)).trans
    (auxiliaryMulCGWH_basepoint.{w} (C := C) (X := X)).symm

/-- The homotopy traces the actual path from the selected unit to the product point. -/
def auxiliaryDiagonalTrace :
    Path (auxiliaryBasepointCGWH.{w} (C := C) (X := X))
      (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).mulUnit :=
  ((auxiliaryDiagonalHomotopyCGWH.{w} (C := C) (X := X)).evalAt
    (auxiliaryBasepointCGWH.{w} (C := C) (X := X))).cast rfl
      (auxiliaryDoublingCGWH_basepoint.{w} (C := C) (X := X)).symm

/-- The unitors provide the actual reverse root path, with no strict multiplication-unit claim. -/
def auxiliaryRootPath :
    Path (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).mulUnit
      (auxiliaryBasepointCGWH.{w} (C := C) (X := X)) :=
  (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).rootPath

/-- The already proved weak-H-space argument gives commutativity of the original pi1. -/
theorem auxiliaryFundamentalGroup_mul_comm
    (p q : FundamentalGroup (auxiliaryCGWH.{w} C X)
      (auxiliaryBasepointCGWH.{w} (C := C) (X := X))) :
    p * q = q * p :=
  CGWH.WeakHSpaceData.fundamentalGroup_mul_comm (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)) p q

end AlgebraicKTheory.AuxiliaryExtension

end


noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction


namespace AlgebraicKTheory.AuxiliaryExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

/-- The actual unit trace is the transported inverse-unitor edge, with its true endpoints. -/
theorem auxiliaryDiagonalTrace_eq_inv_unitor :
    auxiliaryDiagonalTrace.{w} (C := C) (X := X) =
      ((TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk
        (auxiliaryLeftUnitIso.inv.app (auxiliaryUnit C X))))).map
          (auxiliaryCGWHToTopIso.{w} (C := C) (X := X)).inv.hom.continuous).cast
        (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w} (auxiliaryUnit C X))
        ((auxiliaryMulCGWH_basepoint.{w} (C := C) (X := X)).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w}
            (auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X)))) := by
  apply Path.ext
  funext t
  have h := congrArg (fun p => p t)
    (classifyingSpaceCGWHNatTransHomotopy_evalAt.{w}
      (auxiliaryDiagonal (C := C) (X := X)) (auxiliaryUnit C X))
  rewrite [auxiliaryDiagonal_unit_inv] at h
  exact h

/-- The actual root path is the transported common unitor edge. -/
theorem auxiliaryRootPath_eq_unitor :
    auxiliaryRootPath.{w} (C := C) (X := X) =
      ((TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk
        (auxiliaryLeftUnitIso.hom.app (auxiliaryUnit C X))))).map
          (auxiliaryCGWHToTopIso.{w} (C := C) (X := X)).inv.hom.continuous).cast
        ((auxiliaryMulCGWH_basepoint.{w} (C := C) (X := X)).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w}
            (auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X))))
        (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w} (auxiliaryUnit C X)) := rfl

/-- The diagonal homotopy traces the inverse root path; no basepoint-fixed shortcut is used. -/
theorem auxiliaryDiagonalTrace_homotopic_root_symm :
    (auxiliaryDiagonalTrace.{w} (C := C) (X := X)).Homotopic
      (auxiliaryRootPath.{w} (C := C) (X := X)).symm := by
  let D := Auxiliary C X
  let s₀ : auxiliarySpace C X :=
    SSet.realizedVertex (X := nerve D) (nerveEquiv.symm (auxiliaryUnit C X))
  let s₁ : auxiliarySpace C X := SSet.realizedVertex (X := nerve D)
    (nerveEquiv.symm (auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X)))
  let z₀ : auxiliaryCGWH.{w} C X := auxiliaryBasepointCGWH.{w} (C := C) (X := X)
  let z₁ : auxiliaryCGWH.{w} C X :=
    (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).mulUnit
  let e : auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X) ≅
      auxiliaryUnit C X := auxiliaryLeftUnitIso.app (auxiliaryUnit C X)
  let delta : TopCat.of (auxiliaryCGWH.{w} C X) ≅ auxiliarySpace C X :=
    auxiliaryCGWHToTopIso.{w} (C := C) (X := X)
  let f : ContinuousMap (auxiliarySpace C X) (auxiliaryCGWH.{w} C X) := delta.inv.hom
  let p₀ : Path s₀ s₁ :=
    TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.inv))
  let q₀ : Path s₁ s₀ :=
    TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk e.hom))
  let p : Path (f s₀) (f s₁) := p₀.map f.continuous
  let q : Path (f s₁) (f s₀) := q₀.map f.continuous
  have hMapped : p.Homotopic (q₀.symm.map f.continuous) :=
    (CategoryTheory.realizedIso_inv_path e).map f
  have h : p.Homotopic q.symm :=
    (Path.map_symm q₀ f.continuous).symm ▸ hMapped
  have h₀ : z₀ = f s₀ :=
    classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w} (auxiliaryUnit C X)
  have h₁ : z₁ = f s₁ :=
    (auxiliaryMulCGWH_basepoint.{w} (C := C) (X := X)).trans
      (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex.{w}
        (auxiliaryProduct.obj (auxiliaryUnit C X, auxiliaryUnit C X)))
  have hCast : (p.cast h₀ h₁).Homotopic ((q.symm).cast h₀ h₁) := h.pathCast h₀ h₁
  have hTrace : auxiliaryDiagonalTrace.{w} (C := C) (X := X) = p.cast h₀ h₁ :=
    auxiliaryDiagonalTrace_eq_inv_unitor.{w}
  have hRoot : auxiliaryRootPath.{w} (C := C) (X := X) = q.cast h₁ h₀ :=
    auxiliaryRootPath_eq_unitor.{w}
  have hRight : ((q.symm).cast h₀ h₁) =
      (auxiliaryRootPath.{w} (C := C) (X := X)).symm :=
    (Path.cast_symm q h₁ h₀).trans
      (congrArg (fun r : Path z₁ z₀ => r.symm) hRoot.symm)
  exact hTrace.symm ▸ (hRight ▸ hCast)

end AlgebraicKTheory.AuxiliaryExtension

end

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped unitInterval Topology Topology.Homotopy


namespace CGWH.WeakHSpaceData
end CGWH.WeakHSpaceData

end

@[expose] public section

set_option autoImplicit false


noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial Topology

namespace TopCat
end TopCat

end

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped unitInterval Topology Topology.Homotopy


namespace CGWH.WeakHSpaceData
end CGWH.WeakHSpaceData

end

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped unitInterval Topology Topology.Homotopy


namespace TopCat
end TopCat

namespace CGWH.WeakHSpaceData
end CGWH.WeakHSpaceData

end

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.ProjectiveRows

section GenericRows

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

/-- A genuine splitting gives the original canonical-to-given-row Iso. -/
def rowComparison (E : FixedTargetExtension C X) (t : E.toExtension.row.Splitting) :
    AlgebraicKTheory.FixedTargetExtension.SplitInclusion.splitRow
      (C := C) X (⟨E.A⟩ : Core C) ≅ E := by
  let h : AlgebraicKTheory.FixedTargetExtension.SplitInclusion.splitRow
      (C := C) X (⟨E.A⟩ : Core C) ⟶ E :=
    { a := Iso.refl E.A
      b := t.isoBinaryBiproduct.symm
      comm_i := by
        change (biprod.inl : E.A ⟶ E.A ⊞ X) ≫ biprod.desc E.i t.s = 𝟙 E.A ≫ E.i
        exact (biprod.inl_desc _ _).trans (Category.id_comp E.i).symm
      comm_p := by
        change biprod.desc E.i t.s ≫ E.p = (biprod.snd : E.A ⊞ X ⟶ X)
        apply biprod.hom_ext'
        · simp [E.zero]
        · exact ((Category.assoc biprod.inr (biprod.desc E.i t.s) E.p).symm.trans
            ((congrArg (· ≫ E.p) (biprod.inr_desc E.i t.s)).trans t.s_g)).trans
              biprod.inr_snd.symm }
  exact FixedTargetExtension.pairIso h

end GenericRows

section ProjectiveModules

variable {R : Type u} [Ring R] {X : FGProjectiveCat.{v} R}

/-- The original quotient module is genuinely projective for every ring;
the full inclusion introduces no Noetherian restriction. -/
theorem ambientQuotient_projective (X : FGProjectiveCat.{v} R) :
    Projective ((FGProjectiveCat.toModuleCat (R := R)).obj X) := by
  change Projective X.obj
  exact @ModuleCat.projective_of_categoryTheory_projective _ _ X.obj X.property.2

/-- The actual FGProjective admissible row becomes a short exact module row
under the full additive inclusion and its given split exact structure. -/
theorem ambientRow_shortExact (E : FixedTargetExtension (FGProjectiveCat.{v} R) X) :
    (E.toExtension.row.map (FGProjectiveCat.toModuleCat (R := R))).ShortExact := by
  let i := FGProjectiveCat.toModuleCat (R := R)
  have hSplit : isSplitAdmissibleExact E.toExtension.row := E.admissible
  exact shortExact_of_isSplitAdmissibleExact
    (isSplitAdmissibleExact_map (F := i) E.toExtension.row hSplit)

/-- Projectivity derives the ambient quotient section; fullness and
faithfulness lift the actual splitting to the original given row. -/
def projectiveRowSplitting (E : FixedTargetExtension (FGProjectiveCat.{v} R) X) :
    E.toExtension.row.Splitting := by
  let i := FGProjectiveCat.toModuleCat (R := R)
  let S := E.toExtension.row
  letI : Projective ((S.map i).X₃) := ambientQuotient_projective X
  let t : (S.map i).Splitting := (ambientRow_shortExact E).splittingOfProjective
  let r := i.preimage t.r
  let s := i.preimage t.s
  exact
    { r := r
      s := s
      f_r := i.map_injective (by simpa [r, S, ShortComplex.map] using t.f_r)
      s_g := i.map_injective (by simpa [s, S, ShortComplex.map] using t.s_g)
      id := i.map_injective (by simpa [r, s, S, ShortComplex.map] using t.id) }

/-- The all-ring objectwise comparison uses the derived splitting, with no
row-splitting witness supplied to the final projective statement. -/
def projectiveRowComparison (E : FixedTargetExtension (FGProjectiveCat.{v} R) X) :
    AlgebraicKTheory.FixedTargetExtension.SplitInclusion.splitRow
      (C := FGProjectiveCat.{v} R) X (⟨E.A⟩ : Core (FGProjectiveCat.{v} R)) ≅ E :=
  rowComparison E (projectiveRowSplitting E)

end ProjectiveModules

end AlgebraicKTheory.ProjectiveRows

namespace AlgebraicKTheory.AuxiliaryExtension

section OriginalAuxiliary

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

/-- Stabilizing the actual unit by A gives the canonical split row.  Only
the kernel zero unitor is needed; the middle map is the literal identity. -/
def stabilizedUnitIso (X A : C) :
    FixedTargetExtension.leftSumObj (⟨A⟩ : Core C) (unitRow X) ≅
      AlgebraicKTheory.FixedTargetExtension.SplitInclusion.splitRow
        (C := C) X (⟨A⟩ : Core C) := by
  let h : FixedTargetExtension.leftSumObj (⟨A⟩ : Core C) (unitRow X) ⟶
      AlgebraicKTheory.FixedTargetExtension.SplitInclusion.splitRow
        (C := C) X (⟨A⟩ : Core C) :=
    { a := (isoBiprodZero (X := A) (Y := (0 : C)) (isZero_zero C)).symm
      b := Iso.refl (A ⊞ X)
      comm_i := by
        change biprod.map (𝟙 A) (0 : (0 : C) ⟶ X) ≫ 𝟙 (A ⊞ X) =
          (biprod.fst : A ⊞ (0 : C) ⟶ A) ≫ biprod.inl
        apply biprod.hom_ext'
        · simp
        · simp
      comm_p := by
        change 𝟙 (A ⊞ X) ≫ (biprod.snd : A ⊞ X ⟶ X) = biprod.snd ≫ 𝟙 X
        exact (Category.id_comp _).trans (Category.comp_id _).symm }
  exact FixedTargetExtension.pairIso h

/-- The stabilization keeps the exact original middle object and map. -/
theorem stabilizedUnitIso_middle (X A : C) :
    (stabilizedUnitIso X A).hom.b.hom = 𝟙 (A ⊞ X) := rfl

/-- Any actually split row gives a genuine unit-to-row representative in
the original auxiliary category, with stabilizer its original kernel A. -/
def splitUnitRaw (E : FixedTargetExtension C X) (t : E.toExtension.row.Splitting) :
    MonoidalActionCategory.RawHom (auxiliaryUnit C X) (⟨E⟩ : Auxiliary C X) where
  stabilizer := ⟨E.A⟩
  hom := (stabilizedUnitIso X E.A).hom ≫ (ProjectiveRows.rowComparison E t).hom

theorem splitUnitRaw_stabilizer
    (E : FixedTargetExtension C X) (t : E.toExtension.row.Splitting) :
    (splitUnitRaw E t).stabilizer = (⟨E.A⟩ : Core C) := rfl

/-- Its middle component is the original inclusion plus the actual section,
not a changed quotient or a shear-killing stabilization. -/
theorem splitUnitRaw_middle
    (E : FixedTargetExtension C X) (t : E.toExtension.row.Splitting) :
    (splitUnitRaw E t).hom.b.hom = biprod.desc E.i t.s := by
  have h := congrArg Iso.hom
    (FixedTargetExtension.comp_b
      (stabilizedUnitIso X E.A).hom (ProjectiveRows.rowComparison E t).hom)
  change (splitUnitRaw E t).hom.b.hom = 𝟙 (E.A ⊞ X) ≫ biprod.desc E.i t.s at h
  exact h.trans (Category.id_comp _)

end OriginalAuxiliary

section AllRings

variable {R : Type u} [Ring R] (X : FGProjectiveCat.{v} R)

attribute [local instance] FixedTargetExtension.leftSumAction

/-- For every ring and every original row, the actual projective quotient
provides the unit-to-row raw representative. -/
def projectiveUnitRaw (E : FixedTargetExtension (FGProjectiveCat.{v} R) X) :
    MonoidalActionCategory.RawHom (auxiliaryUnit (FGProjectiveCat.{v} R) X)
      (⟨E⟩ : Auxiliary (FGProjectiveCat.{v} R) X) :=
  splitUnitRaw E (ProjectiveRows.projectiveRowSplitting E)

/-- The corresponding arrow is its actual original stabilization class. -/
def projectiveUnitToRow (E : FixedTargetExtension (FGProjectiveCat.{v} R) X) :
    auxiliaryUnit (FGProjectiveCat.{v} R) X ⟶ (⟨E⟩ : Auxiliary (FGProjectiveCat.{v} R) X) :=
  MonoidalActionCategory.Hom.mk (projectiveUnitRaw X E)

/-- The same arrow with an arbitrary original auxiliary object as target. -/
def projectiveUnitToObject (a : Auxiliary (FGProjectiveCat.{v} R) X) :
    auxiliaryUnit (FGProjectiveCat.{v} R) X ⟶ a :=
  projectiveUnitToRow X a.of

/-- Its exact original nerve edge connects the unit vertex to the row vertex. -/
def projectiveUnitEdge (a : Auxiliary (FGProjectiveCat.{v} R) X) :
    (nerve (Auxiliary (FGProjectiveCat.{v} R) X)).Edge
      (nerveEquiv.symm (auxiliaryUnit (FGProjectiveCat.{v} R) X))
      (nerveEquiv.symm a) :=
  CategoryTheory.nerve.edgeMk (projectiveUnitToObject X a)

/-- Realization gives an actual unit-to-row path for every original object. -/
def projectiveUnitPath (a : Auxiliary (FGProjectiveCat.{v} R) X) :
    Path (SSet.realizedVertex (X := nerve (Auxiliary (FGProjectiveCat.{v} R) X))
      (nerveEquiv.symm (auxiliaryUnit (FGProjectiveCat.{v} R) X)))
      (SSet.realizedVertex (X := nerve (Auxiliary (FGProjectiveCat.{v} R) X))
        (nerveEquiv.symm a)) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (projectiveUnitEdge X a))

/-- Every actual simplicial component of L is the component of its unit;
this requires no compatibility between independently chosen splittings. -/
theorem projectiveAuxiliary_piZero_subsingleton :
    Subsingleton (SSet.π₀ (nerve (Auxiliary (FGProjectiveCat.{v} R) X))) := by
  constructor
  intro a b
  obtain ⟨p, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨q, rfl⟩ := SSet.π₀.mk_surjective b
  obtain ⟨E, rfl⟩ := (nerveEquiv (C := Auxiliary (FGProjectiveCat.{v} R) X)).symm.surjective p
  obtain ⟨F, rfl⟩ := (nerveEquiv (C := Auxiliary (FGProjectiveCat.{v} R) X)).symm.surjective q
  exact (SSet.π₀.sound (projectiveUnitEdge X E)).symm.trans
    (SSet.π₀.sound (projectiveUnitEdge X F))

/-- The original auxiliary nerve is connected for every ring and given X. -/
theorem projectiveAuxiliary_nerve_isConnected :
    (nerve (Auxiliary (FGProjectiveCat.{v} R) X)).IsConnected :=
  (SSet.isConnected_iff _).mpr
    ⟨projectiveAuxiliary_piZero_subsingleton X,
      ⟨nerveEquiv.symm (auxiliaryUnit (FGProjectiveCat.{v} R) X)⟩⟩

/-- Genuine simplicial-to-realization component surjectivity yields path
connectedness of the same ordinary realization, including nonvertex points. -/
theorem projectiveAuxiliary_realization_pathConnected :
    PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary (FGProjectiveCat.{v} R) X))) :=
  @SSet.pathConnectedSpace_realization_of_isConnected _
    (projectiveAuxiliary_nerve_isConnected X)

/-- The native space is the actual classifying-space functor applied to L. -/
def projectiveAuxiliaryCGWH :=
  classifyingSpaceCGWH.{w}.obj (Cat.of (Auxiliary (FGProjectiveCat.{v} R) X))

/-- The original ordinary-to-native classifying-space homeomorphism
transports the derived connectedness, without replacing the auxiliary space. -/
theorem projectiveAuxiliaryCGWH_pathConnected :
    PathConnectedSpace (projectiveAuxiliaryCGWH.{w} X) := by
  let delta := classifyingSpaceCGWHToTopIso.{w}.app
    (Cat.of (Auxiliary (FGProjectiveCat.{v} R) X))
  exact @Homeomorph.pathConnectedSpace _ _ _ _
    (projectiveAuxiliary_realization_pathConnected X) (TopCat.homeoOfIso delta.symm)

/-- Every point of the original native auxiliary space is reached from the
actual zero-row vertex by a path, for all rings and all original given X. -/
theorem projectiveAuxiliaryCGWH_unit_joined
    (y : projectiveAuxiliaryCGWH.{w} X) :
    Joined (classifyingSpaceCGWHPoint.{w}
      (auxiliaryUnit (FGProjectiveCat.{v} R) X)) y :=
  @PathConnectedSpace.joined _ _ (projectiveAuxiliaryCGWH_pathConnected.{w} X) _ y

end AllRings

end AlgebraicKTheory.AuxiliaryExtension

end

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

namespace TopCat
end TopCat

namespace SSet
end SSet

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial Topology
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.AuxiliaryExtension

section ExactRows

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] FixedTargetExtension.leftSumAction

/-- The original auxiliary diagonal homotopy, rewritten only by the proved
equality of its actual doubling map with the native product diagonal. -/
def auxiliaryNativeDoublingHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (auxiliaryCGWH.{w} C X))
      (CGWH.cgwhToTop.{w, max u v}.map
        (CGWH.WeakHSpaceData.nativeDoubling
          (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)))).hom := by
  let H := auxiliaryWeakHSpaceData.{w} (C := C) (X := X)
  have hDouble : auxiliaryDoublingCGWH.{w} (C := C) (X := X) =
      CGWH.WeakHSpaceData.nativeDoubling H := auxiliaryDoublingCGWH_eq_mul_diagonal.{w}
  have hMap := congrArg
    (fun f : auxiliaryCGWH.{w} C X ⟶ auxiliaryCGWH.{w} C X =>
      (CGWH.cgwhToTop.{w, max u v}.map f).hom) hDouble
  exact (auxiliaryDiagonalHomotopyCGWH.{w} (C := C) (X := X)).cast rfl hMap

/-- The same original zero-row vertex traces the inverse of the actual
unitor root path; no based-homotopy substitution is used. -/
theorem auxiliaryNativeDoublingTrace :
    (((auxiliaryNativeDoublingHomotopy.{w} (C := C) (X := X)).evalAt
      (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).e).cast rfl
      (CGWH.WeakHSpaceData.nativeDoubling_unit
        (auxiliaryWeakHSpaceData.{w} (C := C) (X := X))).symm).Homotopic
      (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).rootPath.symm := by
  have hPath :
      ((auxiliaryNativeDoublingHomotopy.{w} (C := C) (X := X)).evalAt
        (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).e).cast rfl
        (CGWH.WeakHSpaceData.nativeDoubling_unit
          (auxiliaryWeakHSpaceData.{w} (C := C) (X := X))).symm =
      auxiliaryDiagonalTrace.{w} (C := C) (X := X) := by
    apply Path.ext
    rfl
  rw [hPath]
  exact auxiliaryDiagonalTrace_homotopic_root_symm.{w}

/-- The actual auxiliary weak-unit and diagonal data make its positive
groups at the original unit trivial, already for an arbitrary exact category. -/
theorem auxiliary_positiveGroup_eq_one (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (auxiliaryCGWH.{w} C X)
      (auxiliaryWeakHSpaceData.{w} (C := C) (X := X)).e) : a = 1 :=
  CGWH.WeakHSpaceData.positiveGroup_eq_one
    (auxiliaryWeakHSpaceData.{w} (C := C) (X := X))
    (auxiliaryNativeDoublingHomotopy.{w} (C := C) (X := X))
    (auxiliaryNativeDoublingTrace.{w} (C := C) (X := X)) n a

end ExactRows

section AllRings

variable {R : Type u} [Ring R] (X : FGProjectiveCat.{v} R)

attribute [local instance] FixedTargetExtension.leftSumAction

/-- The derived all-ring connectedness supplies an actual unit-to-point
path; the existing basepoint-change equivalence transports the proved triviality. -/
theorem projectiveAuxiliary_positiveGroup_eq_one_at (n : ℕ)
    (y : auxiliaryCGWH.{w} (FGProjectiveCat.{v} R) X)
    (a : HomotopyGroup.Pi (n + 1) (auxiliaryCGWH.{w} (FGProjectiveCat.{v} R) X) y) : a = 1 := by
  let Y := auxiliaryCGWH.{w} (FGProjectiveCat.{v} R) X
  let H := auxiliaryWeakHSpaceData.{w} (C := FGProjectiveCat.{v} R) (X := X)
  have hConn : PathConnectedSpace Y := projectiveAuxiliaryCGWH_pathConnected.{w} X
  let p : Path H.e y := Classical.choice (@PathConnectedSpace.joined _ _ hConn H.e y)
  let E : HomotopyGroup.Pi (n + 1) Y H.e ≃* HomotopyGroup.Pi (n + 1) Y y :=
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
  have hOne : E.symm a = 1 := auxiliary_positiveGroup_eq_one.{w} n (E.symm a)
  have h1 : a = E (E.symm a) := (E.apply_symm_apply a).symm
  have h2 : E (E.symm a) = E 1 := congrArg E hOne
  have h3 : E 1 = 1 := E.map_one
  exact h1.trans (h2.trans h3)

/-- Every positive homotopy group of the same original projective auxiliary
space is subsingleton at every point, including nonvertices. -/
theorem projectiveAuxiliary_positiveGroup_subsingleton_at (n : ℕ)
    (y : auxiliaryCGWH.{w} (FGProjectiveCat.{v} R) X) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (auxiliaryCGWH.{w} (FGProjectiveCat.{v} R) X) y) := by
  constructor
  intro a b
  exact (projectiveAuxiliary_positiveGroup_eq_one_at.{w} X n y a).trans
    (projectiveAuxiliary_positiveGroup_eq_one_at.{w} X n y b).symm

/-- The actual native-to-ordinary classifying-space Iso carries these
derived trivial groups to the original nerve realization. -/
theorem projectiveAuxiliary_realization_positiveGroup_subsingleton_at (n : ℕ)
    (y : auxiliarySpace (FGProjectiveCat.{v} R) X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (auxiliarySpace (FGProjectiveCat.{v} R) X) y) := by
  let Y := auxiliaryCGWH.{max u (v + 1)} (FGProjectiveCat.{v} R) X
  let Z : TopCat.{max u (v + 1)} := TopCat.of Y
  let d : Z ≅ auxiliarySpace (FGProjectiveCat.{v} R) X :=
    auxiliaryCGWHToTopIso.{max u (v + 1)} (C := FGProjectiveCat.{v} R) (X := X)
  have h : ∀ z : Z, Subsingleton (HomotopyGroup.Pi (n + 1) Z z) :=
    fun z => projectiveAuxiliary_positiveGroup_subsingleton_at.{max u (v + 1)} X n z
  exact TopCat.positiveGroup_subsingleton_of_iso n d h y

/-- For every associative unital ring and every original projective quotient,
the exact terminal map of the original auxiliary nerve is a realization weak equivalence.
Connectedness, positive-group triviality and the map itself are all derived above. -/
theorem projectiveAuxiliary_conull_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve (Auxiliary (FGProjectiveCat.{v} R) X))) :=
  SSet.conull_mem_realizationWeakEquivalences_of_pathConnected_positive
    (nerve (Auxiliary (FGProjectiveCat.{v} R) X))
    (projectiveAuxiliary_realization_pathConnected X)
    (projectiveAuxiliary_realization_positiveGroup_subsingleton_at X)

end AllRings

end AlgebraicKTheory.AuxiliaryExtension

end
