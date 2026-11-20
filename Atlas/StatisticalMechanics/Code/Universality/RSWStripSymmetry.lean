/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Code.RSW.SelfDuality
import Code.Universality.FrameChangeIso

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice





def rss_stripReflectFun (n : ℤ) (x : Site 2) : Site 2 :=
  ![x 0 + 1, 2 * n - 1 - x 1]


def rss_stripReflectInvFun (n : ℤ) (x : Site 2) : Site 2 :=
  ![x 0 - 1, 2 * n - 1 - x 1]


def rss_stripReflect (n : ℤ) : Site 2 ≃ Site 2 where
  toFun := rss_stripReflectFun n
  invFun := rss_stripReflectInvFun n
  left_inv x := by
    ext i
    fin_cases i <;> simp [rss_stripReflectFun, rss_stripReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rss_stripReflectFun, rss_stripReflectInvFun]

@[simp] theorem rss_stripReflect_zero (n : ℤ) (x : Site 2) :
    rss_stripReflect n x 0 = x 0 + 1 := by
  rfl

@[simp] theorem rss_stripReflect_one (n : ℤ) (x : Site 2) :
    rss_stripReflect n x 1 = 2 * n - 1 - x 1 := by
  rfl

@[simp] theorem rss_stripReflect_symm_zero (n : ℤ) (x : Site 2) :
    (rss_stripReflect n).symm x 0 = x 0 - 1 := by
  rfl

@[simp] theorem rss_stripReflect_symm_one (n : ℤ) (x : Site 2) :
    (rss_stripReflect n).symm x 1 = 2 * n - 1 - x 1 := by
  rfl


theorem rss_adj_stripReflect (n : ℤ) (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rss_stripReflect n x) (rss_stripReflect n y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rss_stripReflect_zero, rss_stripReflect_one]
  rw [show (x 0 + 1) - (y 0 + 1) = x 0 - y 0 by ring,
    show (2 * n - 1 - x 1) - (2 * n - 1 - y 1) = -(x 1 - y 1) by ring,
    Int.natAbs_neg]


def rss_faceStrip (n : ℤ) : Set (Site 2) :=
  {x | -n ≤ x 1 ∧ x 1 ≤ 3 * n - 1}


def rss_bottomFaceLine (n : ℤ) : Set (Site 2) := {x | x 1 = -n}


def rss_topFaceLine (n : ℤ) : Set (Site 2) := {x | x 1 = 3 * n - 1}


theorem rss_mem_faceStrip_reflect (n : ℤ) (x : Site 2) :
    x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n := by
  simp only [rss_faceStrip, Set.mem_setOf_eq, rss_stripReflect_one]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> omega


theorem rss_mem_bottom_reflect_iff_top (n : ℤ) (x : Site 2) :
    x ∈ rss_bottomFaceLine n ↔ rss_stripReflect n x ∈ rss_topFaceLine n := by
  simp [rss_bottomFaceLine, rss_topFaceLine]
  omega


theorem rss_mem_top_reflect_iff_bottom (n : ℤ) (x : Site 2) :
    x ∈ rss_topFaceLine n ↔ rss_stripReflect n x ∈ rss_bottomFaceLine n := by
  simp [rss_bottomFaceLine, rss_topFaceLine]
  omega




inductive rss_StripEnd
  | bottom
  | top
  deriving DecidableEq, Repr


def rss_reflectEnd : rss_StripEnd → rss_StripEnd
  | .bottom => .top
  | .top => .bottom


def rss_halfWiredBoundary : rss_StripEnd → BoundaryCondition
  | .bottom => .free
  | .top => .wired



theorem rss_dual_reflected_halfWiredBoundary (e : rss_StripEnd) :
    RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) =
      rss_halfWiredBoundary e := by
  cases e <;> rfl




noncomputable def rss_stripReflectEdge (n : ℤ) :
    Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  sym2Congr (rss_stripReflect n)


noncomputable def rss_reflectConfig (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) (rss_stripReflectEdge n) omega

theorem rss_reflectConfig_apply (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rss_reflectConfig n omega e =
      omega (e.map (rss_stripReflect n).symm) := by
  rw [rss_reflectConfig, Equiv.piCongrLeft_apply]
  simp [rss_stripReflectEdge, sym2Congr]


theorem rss_reflectConfig_measurePreserving (n : ℤ) :
    MeasurePreserving (rss_reflectConfig n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  refine ⟨(MeasurableEquiv.piCongrLeft
    (fun _ => Bool) (rss_stripReflectEdge n)).measurable, ?_⟩
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) =>
      bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
    (rss_stripReflectEdge n)



noncomputable def rss_stripDualReflection (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  rss_reflectConfig n (fci_faceDualConfig omega)



theorem rss_stripDualReflection_apply (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rss_stripDualReflection n omega e =
      !(omega (fci_faceEdgeEquiv
        (e.map (rss_stripReflect n).symm))) := by
  rw [rss_stripDualReflection, rss_reflectConfig_apply, fci_faceDualConfig]



theorem rss_stripDualReflection_measurePreserving (n : ℤ) :
    MeasurePreserving (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  exact (rss_reflectConfig_measurePreserving n).comp
    fci_faceDualConfig_measurePreserving



theorem rss_stripDualReflection_law (n : ℤ) :
    Measure.map (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) =
      bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one :=
  (rss_stripDualReflection_measurePreserving n).map_eq





theorem rss_strip_symmetry (n : ℤ) :
    (∀ x : Site 2,
      x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n) ∧
    (∀ x : Site 2,
      x ∈ rss_bottomFaceLine n ↔
        rss_stripReflect n x ∈ rss_topFaceLine n) ∧
    (∀ x : Site 2,
      x ∈ rss_topFaceLine n ↔
        rss_stripReflect n x ∈ rss_bottomFaceLine n) ∧
    (∀ e : rss_StripEnd,
      RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) =
        rss_halfWiredBoundary e) ∧
    MeasurePreserving (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  exact ⟨rss_mem_faceStrip_reflect n,
    rss_mem_bottom_reflect_iff_top n,
    rss_mem_top_reflect_iff_bottom n,
    rss_dual_reflected_halfWiredBoundary,
    rss_stripDualReflection_measurePreserving n⟩

end Universality

end StatMech
