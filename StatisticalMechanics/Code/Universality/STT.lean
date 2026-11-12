/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Foundations.ProductMeasure
import Code.Lattice.PlanarDual

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace StatMech

namespace Universality










def kappaSquare (p0 p1 : ℝ) : ℝ := p0 + p1 - 1



def kappaTri (p0 p1 p2 : ℝ) : ℝ := p0 + p1 + p2 - p0 * p1 * p2 - 1



def kappaHex (p0 p1 p2 : ℝ) : ℝ := -kappaTri (1 - p0) (1 - p1) (1 - p2)



def IsCriticalSquare (p0 p1 : ℝ) : Prop := kappaSquare p0 p1 = 0




def IsCriticalTri (p0 p1 p2 : ℝ) : Prop := kappaTri p0 p1 p2 = 0


def IsCriticalHex (p0 p1 p2 : ℝ) : Prop := kappaHex p0 p1 p2 = 0


theorem isCriticalSquare_iff (p0 p1 : ℝ) : IsCriticalSquare p0 p1 ↔ p0 + p1 = 1 := by
  unfold IsCriticalSquare kappaSquare; constructor <;> intro h <;> linarith


theorem isCriticalTri_iff (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ p0 + p1 + p2 - p0 * p1 * p2 = 1 := by
  unfold IsCriticalTri kappaTri; constructor <;> intro h <;> linarith






theorem isCriticalTri_iff_isCriticalHex_compl (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ IsCriticalHex (1 - p0) (1 - p1) (1 - p2) := by
  unfold IsCriticalTri IsCriticalHex kappaHex
  simp only [sub_sub_cancel]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith [neg_eq_zero.mp h]












def edgeWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem edgeWeight_true (p : ℝ) : edgeWeight p true = p := rfl
@[simp] theorem edgeWeight_false (p : ℝ) : edgeWeight p false = 1 - p := rfl



abbrev LocalConfig : Type := Bool × Bool × Bool





def localWeight (p0 p1 p2 : ℝ) (ω : LocalConfig) : ℝ :=
  edgeWeight p0 ω.1 * edgeWeight p1 ω.2.1 * edgeWeight p2 ω.2.2




theorem sum_localWeight (p0 p1 p2 : ℝ) :
    ∑ ω : LocalConfig, localWeight p0 p1 p2 ω = 1 := by
  simp only [localWeight, edgeWeight, Fintype.sum_prod_type, Fintype.sum_bool, if_true,
    if_neg (by decide : ¬ (false = true))]
  ring












def triAB (ω : LocalConfig) : Bool := ω.2.2 || (ω.1 && ω.2.1)

def triAC (ω : LocalConfig) : Bool := ω.2.1 || (ω.1 && ω.2.2)

def triBC (ω : LocalConfig) : Bool := ω.1 || (ω.2.1 && ω.2.2)


def starAB (ω : LocalConfig) : Bool := ω.1 && ω.2.1

def starAC (ω : LocalConfig) : Bool := ω.1 && ω.2.2

def starBC (ω : LocalConfig) : Bool := ω.2.1 && ω.2.2




def triPatABC (ω : LocalConfig) : Bool := triAB ω && triBC ω && triAC ω

def starPatABC (ω : LocalConfig) : Bool := starAB ω && starBC ω && starAC ω

def triPatSep (ω : LocalConfig) : Bool := !triAB ω && !triBC ω && !triAC ω

def starPatSep (ω : LocalConfig) : Bool := !starAB ω && !starBC ω && !starAC ω

def triPatAB (ω : LocalConfig) : Bool := triAB ω && !triAC ω && !triBC ω

def starPatAB (ω : LocalConfig) : Bool := starAB ω && !starAC ω && !starBC ω

def triPatAC (ω : LocalConfig) : Bool := triAC ω && !triAB ω && !triBC ω

def starPatAC (ω : LocalConfig) : Bool := starAC ω && !starAB ω && !starBC ω

def triPatBC (ω : LocalConfig) : Bool := triBC ω && !triAB ω && !triAC ω

def starPatBC (ω : LocalConfig) : Bool := starBC ω && !starAB ω && !starAC ω




def triProb (p0 p1 p2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight p0 p1 p2 ω else 0




def starProb (q0 q1 q2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight q0 q1 q2 ω else 0



private theorem prob_def (p0 p1 p2 : ℝ) (pat : LocalConfig → Bool) :
    triProb p0 p1 p2 pat = starProb p0 p1 p2 pat := rfl










theorem stt_AB (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAB, starPatAB,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num


theorem stt_AC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAC, starPatAC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num


theorem stt_BC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatBC, starPatBC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num











theorem stt_ABC_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatABC - starProb (1 - p0) (1 - p1) (1 - p2) starPatABC
      = kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatABC, starPatABC,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring




theorem stt_Sep_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatSep - starProb (1 - p0) (1 - p1) (1 - p2) starPatSep
      = -kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatSep, starPatSep,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring



theorem stt_ABC (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC := by
  have := stt_ABC_sub p0 p1 p2
  rw [h] at this; linarith


theorem stt_Sep (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep := by
  have := stt_Sep_sub p0 p1 p2
  rw [h] at this; linarith















theorem starTriangle_connectivity (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC ∧
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep ∧
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB ∧
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC ∧
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC :=
  ⟨stt_ABC p0 p1 p2 h, stt_Sep p0 p1 p2 h, stt_AB p0 p1 p2, stt_AC p0 p1 p2,
    stt_BC p0 p1 p2⟩





theorem isCriticalTri_of_starTriangle (p0 p1 p2 : ℝ)
    (h : triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) :
    IsCriticalTri p0 p1 p2 := by
  have := stt_ABC_sub p0 p1 p2
  rw [h, sub_self] at this
  exact this.symm





theorem starTriangle_iff_isCriticalTri (p0 p1 p2 : ℝ) :
    (triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) ↔
      IsCriticalTri p0 p1 p2 :=
  ⟨isCriticalTri_of_starTriangle p0 p1 p2, stt_ABC p0 p1 p2⟩














theorem bernoulliMeasure_map_not (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun b => !b) (bernoulliMeasure p hp)
      = bernoulliMeasure (1 - p) tsub_le_self := by
  have hmeas : Measurable (fun b : Bool => !b) := measurable_of_countable _
  refine (MeasureTheory.Measure.ext_iff_singleton).2 ?_
  intro x
  rw [Measure.map_apply hmeas (measurableSet_singleton x)]
  cases x with
  | false =>
    have hpre : (fun b => !b) ⁻¹' ({false} : Set Bool) = ({true} : Set Bool) := by
      ext b; cases b <;> simp
    have harith : (1 : ℝ≥0) - (1 - p) = p := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub tsub_le_self, NNReal.coe_sub hp]; ring
    rw [bernoulliMeasure_apply_false, harith, hpre, bernoulliMeasure_apply_true]
  | true =>
    have hpre : (fun b => !b) ⁻¹' ({true} : Set Bool) = ({false} : Set Bool) := by
      ext b; cases b <;> simp
    rw [bernoulliMeasure_apply_true, hpre, bernoulliMeasure_apply_false,
      ENNReal.coe_sub, ENNReal.coe_one]




theorem one_sub_half : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (by norm_num)]; push_cast; norm_num


theorem half_le_one : (2 : ℝ≥0)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (by norm_num)]; norm_num





theorem bernoulli_selfDual_half :
    Measure.map (fun b => !b) (bernoulliMeasure 2⁻¹ half_le_one)
      = bernoulliMeasure 2⁻¹ half_le_one := by
  rw [bernoulliMeasure_map_not]
  congr 1
  exact one_sub_half







theorem primal_open_iff_dual_closed (ω : ConfigSpace (Sym2 (Lattice.Site 2)))
    (e : Sym2 (Lattice.Site 2)) :
    ω e = true ↔ Lattice.dualConfig ω (Lattice.crossEdge e) = false :=
  Lattice.isOpen_iff_dual_isClosed ω e

end Universality

end StatMech
