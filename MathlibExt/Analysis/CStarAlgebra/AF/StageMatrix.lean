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

public import MathlibExt.Analysis.CStarAlgebra.AF.Basic
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Matrix approximation in a dense increasing C-star exhaustion

The coefficient stages are actual closed star subalgebras of the original
complete nonunital coefficient algebra. All matrix norms and entry values
are inherited from those original dictionaries. A finite collection of
entry approximations is placed in one actual common stage.
-/

@[expose] public section

noncomputable section

open Set Finset
open scoped CStarAlgebra BigOperators

namespace CStarAlgebra

universe uA uM uN

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

/-- **Matrix approximation in a dense increasing family.** Let `A` be a nonunital complex C*-algebra and
let `Aₖ ⊆ A`, for `k ∈ ℕ`, be increasing closed nonunital star subalgebras with norm-dense union.
For finite index types `m,n`, every `M ∈ Mₘ,ₙ(A)` and `ε > 0` admit a matrix in one `Mₘ,ₙ(Aₖ)` whose
image is within `ε` of `M` in the C*-matrix norm. Empty indices and the zero algebra are included. -/
theorem exists_stage_matrix_near
    (stage : ℕ → NonUnitalStarSubalgebra ℂ A)
    [∀ k, IsClosed (stage k : Set A)]
    (hmono : Monotone stage)
    (hdense : Dense (⋃ k, (stage k : Set A)))
    (M : CStarMatrix m n A) (ε : ℝ) (hε : 0 < ε) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    ∃ k : ℕ, ∃ X : CStarMatrix m n (stage k),
      ‖M - CStarMatrix.mapₗ
        (NonUnitalStarSubalgebraClass.subtype (stage k) : stage k →ₗ[ℂ] A) X‖ < ε := by
  classical
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : ∀ k, NonUnitalCStarAlgebra (stage k) := fun k =>
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (stage k)
  let C : ℝ := (Fintype.card n : ℝ) * (Fintype.card m : ℝ)
  let δ : ℝ := ε / (C + 1)
  have hC : 0 ≤ C := by positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hchoice (p : m × n) : ∃ k : ℕ, ∃ a : A, a ∈ stage k ∧ ‖M p.1 p.2 - a‖ < δ := by
    obtain ⟨a, ha, hnear⟩ := hdense.exists_dist_lt (M p.1 p.2) hδ
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    exact ⟨k, a, hk, by simpa only [dist_eq_norm] using hnear⟩
  let index (p : m × n) : ℕ := Classical.choose (hchoice p)
  let value (p : m × n) : A := Classical.choose (Classical.choose_spec (hchoice p))
  have hvalue (p : m × n) : value p ∈ stage (index p) ∧ ‖M p.1 p.2 - value p‖ < δ :=
    Classical.choose_spec (Classical.choose_spec (hchoice p))
  let k := Finset.univ.sup index
  have hmem (p : m × n) : value p ∈ stage k :=
    hmono (Finset.le_sup (f := index) (Finset.mem_univ p)) (hvalue p).1
  let X : CStarMatrix m n (stage k) :=
    CStarMatrix.ofMatrix (fun i j => ⟨value (i, j), hmem (i, j)⟩)
  refine ⟨k, X, ?_⟩
  have hentries (i : m) (j : n) :
      ‖(M - CStarMatrix.mapₗ
        (NonUnitalStarSubalgebraClass.subtype (stage k) : stage k →ₗ[ℂ] A) X) i j‖ ≤ δ := by
    change ‖M i j - value (i, j)‖ ≤ δ
    exact (hvalue (i, j)).2.le
  have hnorm : ‖M - CStarMatrix.mapₗ
      (NonUnitalStarSubalgebraClass.subtype (stage k) : stage k →ₗ[ℂ] A) X‖ ≤ C * δ := by
    calc
      _ ≤ ∑ j, ∑ i,
          ‖(M - CStarMatrix.mapₗ
            (NonUnitalStarSubalgebraClass.subtype (stage k) : stage k →ₗ[ℂ] A) X) i j‖ :=
        CStarMatrix.norm_le_sum_norm_entries _
      _ ≤ ∑ _j : n, ∑ _i : m, δ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hentries i j
      _ = C * δ := by simp [C, mul_assoc]
  have hscale : δ * (C + 1) = ε := by
    dsimp only [δ]
    exact div_mul_cancel₀ ε (by positivity)
  exact hnorm.trans_lt (by nlinarith)

end CStarAlgebra
