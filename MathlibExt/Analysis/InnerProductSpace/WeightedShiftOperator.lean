/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpDiagonalOperator
public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-!
# Weighted unilateral shifts on `ℓ²(ℕ, 𝕜)`

For bounded weights `w : ℕ → 𝕜`, the weighted forward shift inserts zero
at coordinate `0` and sends input coordinate `n` to output coordinate
`n + 1`, multiplied by `w n`. Its weighted backward shift uses conjugated
weights: output coordinate `i` is `conj (w i) * x (i + 1)`.

The construction uses the canonical operators in `LpShiftOperator` and
`LpDiagonalOperator`. The forward operator is diagonal multiplication
followed by the plain forward shift. The backward operator is the plain
backward shift followed by diagonal multiplication with conjugated weights.
The linear-map interfaces are projections of these continuous linear maps.
The shared diagonal construction specializes the Hilbert-basis operator in
`HilbertBasisDiagonal` to the identity coordinates of `ℓ²`.

Both operator norms equal the supremum `⨆ n, ‖w n‖`. The backward operator
is the adjoint of the forward operator. Their two composites act diagonally
by squared weight moduli, with the forward-after-backward composite killing
coordinate `0`. The forward operator is an isometry exactly when every
weight has modulus `1`; it is injective when no weight vanishes and is not
injective when a weight vanishes. The companion `WeightedShiftCompact`
module proves compactness exactly when the weights tend to zero and contains
subtraction and prefix-truncation results.

These are derived supporting results using the canonical lp factors.
The archived Hilbert-space and spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` provides
related source context; it is not an exact source proof for the weighted results.

## Main declarations

* `weightedShiftFun` / `weightedBackwardFun`: the pointwise shift functions.
* `weightedShiftCLM` / `weightedBackwardCLM`: the canonical bounded compositions.
* `weightedShiftLinMap` / `weightedBackwardLinMap`: their linear-map projections.
* `norm_weightedShiftCLM` / `norm_weightedBackwardCLM`: norms as the weight supremum.
* `adjoint_weightedShiftCLM`: the adjoint is the conjugated backward operator.
* `backward_comp_shift_apply` / `shift_comp_backward_apply`: squared-modulus composites.
* `isometry_weightedShiftCLM_iff`: isometry exactly for unit-modulus weights.
* `injective_weightedShiftCLM` / `not_injective_weightedShiftCLM`: the zero-weight boundary.
* `weightedShiftCLM_one` / `weightedBackwardCLM_one`: equalities to the canonical plain shifts.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator

open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal ComplexConjugate
open MathlibExt.Analysis.InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Weighted forward shift of a sequence.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For a weight sequence $w : \mathbb{N} \to \mathbb{K}$ and a sequence
$x : \mathbb{N} \to \mathbb{K}$, the weighted forward shift of $x$ is the sequence $y$ with
$y_0 = 0$ and $y_{n+1} = w_n x_n$ for every $n \in \mathbb{N}$. -/
def weightedShiftFun (w : ℕ → 𝕜) (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => w n * x n

/-- **Weighted backward shift of a sequence.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
For weights $w : \mathbb{N} \to \mathbb{K}$ and a sequence $x : \mathbb{N} \to \mathbb{K}$, the
weighted backward shift of $x$ is the sequence whose term at index $i$ is
$\overline{w_i}\, x_{i+1}$.

The weights are conjugated so that the resulting operator on $\ell^2$ is the adjoint of the
weighted forward shift. -/
def weightedBackwardFun (w : ℕ → 𝕜) (x : ℕ → 𝕜) (i : ℕ) : 𝕜 :=
  conj (w i) * x (i + 1)

/-- **Weighted forward shift at index zero.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
For all weights $w : \mathbb{N} \to \mathbb{K}$ and every sequence $x : \mathbb{N} \to \mathbb{K}$,
the term at index $0$ of the weighted forward shift of $x$ is $0$. -/
@[simp] theorem weightedShiftFun_zero (w : ℕ → 𝕜) (x : ℕ → 𝕜) :
    weightedShiftFun w x 0 = 0 := rfl

/-- **Weighted forward shift at a successor index.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For weights $w : \mathbb{N} \to \mathbb{K}$, a sequence
$x : \mathbb{N} \to \mathbb{K}$ and $n \in \mathbb{N}$, the term at index $n + 1$ of the weighted
forward shift of $x$ is $w_n x_n$. -/
@[simp] theorem weightedShiftFun_succ (w : ℕ → 𝕜) (x : ℕ → 𝕜) (n : ℕ) :
    weightedShiftFun w x (n + 1) = w n * x n := rfl

/-- **Coordinates of the weighted backward-shift function.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For weights $w : \mathbb{N} \to \mathbb{K}$, a sequence
$x : \mathbb{N} \to \mathbb{K}$ and $i \in \mathbb{N}$, the weighted backward-shift function of
$w$ applied to $x$ takes the value $\overline{w_i}\, x_{i+1}$ at $i$. -/
@[simp] theorem weightedBackwardFun_apply (w : ℕ → 𝕜) (x : ℕ → 𝕜) (i : ℕ) :
    weightedBackwardFun w x i = conj (w i) * x (i + 1) := rfl

/-- Convert bounded weight norms to the uniform bound expected by the diagonal API. -/
private theorem exists_uniform_bound {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ∃ C, ∀ n, ‖w n‖ ≤ C := by
  simpa only [bddAbove_def, Set.forall_mem_range] using hw

/-- **Weighted forward shift operator.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$w : \mathbb{N} \to \mathbb{K}$ be weights with $\sup_n |w_n| < \infty$. The weighted forward
shift with weights $w$ is the bounded operator on $\ell^2(\mathbb{N}, \mathbb{K})$ obtained by
first applying the diagonal operator $x \mapsto (w_n x_n)_{n}$ and then the unilateral forward
shift $(x_0, x_1, \dots) \mapsto (0, x_0, x_1, \dots)$. -/
noncomputable def weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  LpShiftOperator.shiftCLM ∘L LpDiagonalOperator.diagonalCLM w (by
    exact exists_uniform_bound hw)

/-- **Weighted backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli. The weighted backward shift $B_w$
is the bounded operator on $\ell^2(\mathbb{N}, \mathbb{K})$ obtained by applying the backward shift
$(x_0, x_1, \dots) \mapsto (x_1, x_2, \dots)$ and then multiplying coordinate $i$ by
$\overline{w_i}$; thus $(B_w x)_i = \overline{w_i}\, x_{i+1}$. -/
noncomputable def weightedBackwardCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  LpDiagonalOperator.diagonalCLM (fun n => star (w n)) (by
    simpa only [norm_star] using exists_uniform_bound hw) ∘L
    LpShiftOperator.backwardCLM

/-- **Weighted forward shift as a linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $w : \mathbb{N} \to \mathbb{K}$ be a weight sequence whose norms
$\|w_n\|$ are bounded above. The weighted forward shift linear map is the $\mathbb{K}$-linear
map $\ell^2(\mathbb{N}, \mathbb{K}) \to \ell^2(\mathbb{N}, \mathbb{K})$ underlying the bounded
weighted forward shift operator (multiplication by $w$ followed by the forward shift), which
sends $x$ to the sequence $y$ with $y_0 = 0$ and $y_{n+1} = w_n x_n$. -/
noncomputable abbrev weightedShiftLinMap (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
  (weightedShiftCLM w hw).toLinearMap

/-- **Weighted backward shift as a linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$
and let $w : \mathbb{N} \to \mathbb{K}$ be weights with $\sup_n |w_n| < \infty$. The weighted
backward shift linear map with weights $w$ is the bounded weighted backward shift operator on
$\ell^2(\mathbb{N}, \mathbb{K})$ with weights $w$, regarded as a $\mathbb{K}$-linear map from
$\ell^2(\mathbb{N}, \mathbb{K})$ to itself (forgetting continuity). -/
noncomputable abbrev weightedBackwardLinMap (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
  (weightedBackwardCLM w hw).toLinearMap

/-- **Coordinates of the weighted forward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with $\sup_n |w_n| < \infty$, and let
$S_w$ be the weighted forward shift operator on $\ell^2(\mathbb{N}, \mathbb{K})$ with weights $w$.
For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$, the coordinate
$(S_w x)_i$ is the term at index $i$ of the weighted forward shift of the sequence $x$; that is,
$(S_w x)_0 = 0$ and $(S_w x)_{n+1} = w_n x_n$. -/
theorem weightedShiftCLM_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    weightedShiftCLM w hw x i = weightedShiftFun w (x : ℕ → 𝕜) i := by
  cases i <;> simp [weightedShiftCLM, weightedShiftFun,
    LpShiftOperator.shiftCLM_apply, LpDiagonalOperator.diagonalCLM_apply,
    LpShiftOperator.shiftFun]

/-- **Coordinates of the weighted backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli, and let $B_w$ be
the weighted backward shift on $\ell^2(\mathbb{N}, \mathbb{K})$. For every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$, the $i$-th coordinate of
$B_w x$ is the weighted backward-shift function of $w$ applied to $x$ at $i$, that is,
$(B_w x)_i = \overline{w_i}\, x_{i+1}$. -/
theorem weightedBackwardCLM_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    weightedBackwardCLM w hw x i = weightedBackwardFun w (x : ℕ → 𝕜) i := by
  simp [weightedBackwardCLM, weightedBackwardFun,
    LpDiagonalOperator.diagonalCLM_apply, LpShiftOperator.backwardCLM_apply,
    LpShiftOperator.backwardFun, RCLike.star_def]

/-- **The weighted forward shift agrees with the shift of sequences.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and let $w : \mathbb{N} \to \mathbb{K}$ be weights with
$\sup_n |w_n| < \infty$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the image of $x$ under
the weighted forward shift operator with weights $w$ is as a sequence the weighted forward
shift of $x$: its term at index $0$ is $0$ and its term at index $n + 1$ is $w_n x_n$ for
every $n$. -/
theorem weightedShiftCLM_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedShiftCLM w hw x) = weightedShiftFun w (x : ℕ → 𝕜) := by
  funext i; exact weightedShiftCLM_apply w hw x i

/-- **Coordinates of the weighted forward shift linear map.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and let $w : \mathbb{N} \to \mathbb{K}$ be a weight sequence
whose norms $\|w_n\|$ are bounded above. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the
image of $x$ under the weighted forward shift linear map, viewed as a sequence, is the weighted
forward shift of $x$: its coordinate $0$ is $0$ and its coordinate $n + 1$ is $w_n x_n$ for
every $n$. -/
theorem weightedShiftLinMap_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedShiftLinMap w hw x) = weightedShiftFun w (x : ℕ → 𝕜) :=
  weightedShiftCLM_apply_coe w hw x

/-- **The weighted backward shift linear map agrees with the shift of sequences.** Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $w : \mathbb{N} \to \mathbb{K}$ be weights with
$\sup_n |w_n| < \infty$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the image of $x$ under
the weighted backward shift with weights $w$, regarded as a linear map on
$\ell^2(\mathbb{N}, \mathbb{K})$, is as a sequence the weighted backward shift of $x$: its term
at index $i$ is $\overline{w_i}\, x_{i+1}$ for every $i$. -/
theorem weightedBackwardLinMap_apply_coe (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ⇑(weightedBackwardLinMap w hw x) = weightedBackwardFun w (x : ℕ → 𝕜) := by
  funext i; exact weightedBackwardCLM_apply w hw x i

/-- **Weighted forward shifts preserve square-summability.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$. For every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$, the sequence $y$ with $y_0 = 0$ and
$y_{n+1} = w_n x_n$ is square-summable. -/
theorem memℓp_weightedShiftFun {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (weightedShiftFun w (x : ℕ → 𝕜)) 2 := by
  rw [← weightedShiftCLM_apply_coe w hw x]
  exact lp.memℓp _

/-- **Weighted backward shifts preserve square-summability.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$. For every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$, the sequence $(\overline{w_i}\, x_{i+1})_{i \in \mathbb{N}}$
is square-summable. -/
theorem memℓp_weightedBackwardFun {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (weightedBackwardFun w (x : ℕ → 𝕜)) 2 := by
  rw [← weightedBackwardLinMap_apply_coe w hw x]
  exact lp.memℓp _

/-- **The weighted forward shift on basis vectors.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with $\sup_n |w_n| < \infty$, and let
$(e_n)_{n \in \mathbb{N}}$ be the standard basis vectors of $\ell^2(\mathbb{N}, \mathbb{K})$. For
every $n$, the weighted forward shift operator with weights $w$ sends $e_n$ to $w_n e_{n+1}$. -/
theorem weightedShiftCLM_single (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) :
    weightedShiftCLM w hw (lp.single 2 n (1 : 𝕜)) = lp.single 2 (n + 1) (w n) := by
  apply lp.ext; funext i
  cases i with
  | zero => simp [weightedShiftCLM_apply]
  | succ m => by_cases h : m = n <;> simp [weightedShiftCLM_apply, h]

/-- **Weighted backward shift on basis vectors.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli, and write $e_n$
for the $n$-th standard basis vector of $\ell^2(\mathbb{N}, \mathbb{K})$. For every $n$, the
weighted backward shift $B_w$ satisfies $B_w e_{n+1} = \overline{w_n}\, e_n$. -/
theorem weightedBackwardCLM_single_succ (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) :
    weightedBackwardCLM w hw (lp.single 2 (n + 1) (1 : 𝕜)) =
      lp.single 2 n (conj (w n)) := by
  apply lp.ext; funext i
  by_cases h : i = n <;> simp [weightedBackwardCLM_apply, h]

/-- **Uniform weight bounds bound the weighted shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli, and let $S_w$ be
the weighted forward shift on $\ell^2(\mathbb{N}, \mathbb{K})$. If $C$ is a real number with
$|w_n| \le C$ for every $n$, then the operator norm of $S_w$ is at most $C$. -/
theorem norm_weightedShiftCLM_le_of_forall_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {C : ℝ} (hC : ∀ n, ‖w n‖ ≤ C) :
    ‖weightedShiftCLM w hw‖ ≤ C := by
  rw [weightedShiftCLM]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    rw [LpShiftOperator.norm_shiftCLM, one_mul]
    exact LpDiagonalOperator.norm_diagonalCLM_le w (exists_uniform_bound hw)
      (le_trans (norm_nonneg (w 0)) (hC 0)) hC)

/-- **Operator norm of a weighted shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and
let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli. The weighted forward shift
$S_w$ on $\ell^2(\mathbb{N}, \mathbb{K})$ has operator norm $\|S_w\| = \sup_n |w_n|$. -/
theorem norm_weightedShiftCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    ‖weightedShiftCLM w hw‖ = ⨆ n, ‖w n‖ := by
  apply le_antisymm
  · rw [weightedShiftCLM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (by
      rw [LpShiftOperator.norm_shiftCLM, one_mul,
        LpDiagonalOperator.norm_diagonalCLM])
  · apply ciSup_le
    intro n
    have h1 := ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜)
      (f := weightedShiftCLM w hw) (x := lp.single 2 n (1 : 𝕜))
    rw [weightedShiftCLM_single, lp.norm_single (by norm_num),
      lp.norm_single (by norm_num), norm_one, mul_one] at h1
    exact h1

/-- **Adjoint of the weighted shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$. The adjoint of the weighted
forward shift $S_w$ on $\ell^2(\mathbb{N}, \mathbb{K})$, given by $(S_w x)_0 = 0$ and
$(S_w x)_{n+1} = w_n x_n$, is the weighted backward shift $B_w$, given by
$(B_w x)_i = \overline{w_i}\, x_{i+1}$; that is, $S_w^* = B_w$. -/
theorem adjoint_weightedShiftCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    (weightedShiftCLM w hw)† = weightedBackwardCLM w hw := by
  rw [weightedShiftCLM, ContinuousLinearMap.adjoint_comp,
    LpShiftOperator.adjoint_shiftCLM, LpDiagonalOperator.adjoint_diagonalCLM]
  rfl

/-- **Norm of the weighted backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and
let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$. The weighted backward shift
$B_w$ on $\ell^2(\mathbb{N}, \mathbb{K})$, given by $(B_w x)_i = \overline{w_i}\, x_{i+1}$, has
operator norm $\|B_w\| = \sup_n |w_n|$. -/
theorem norm_weightedBackwardCLM {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    ‖weightedBackwardCLM w hw‖ = ⨆ n, ‖w n‖ := by
  apply le_antisymm
  · rw [weightedBackwardCLM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left LpShiftOperator.norm_backwardCLM_le (norm_nonneg _)).trans_eq
        (by rw [LpDiagonalOperator.norm_diagonalCLM, mul_one]; simp only [norm_star]))
  · apply ciSup_le
    intro n
    have h1 := ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜)
      (f := weightedBackwardCLM w hw) (x := lp.single 2 (n + 1) (1 : 𝕜))
    rw [weightedBackwardCLM_single_succ, lp.norm_single (by norm_num), RCLike.norm_conj,
      lp.norm_single (by norm_num), norm_one, mul_one] at h1
    exact h1

/-- **Norm bound for weighted shift images.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and
let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli. For every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$, the weighted forward shift $S_w$, viewed as a linear map,
satisfies $\|S_w x\| \le \left(\sup_n |w_n|\right) \|x\|$. -/
theorem norm_weightedShiftLinMap_apply_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ‖weightedShiftLinMap w hw x‖ ≤ (⨆ n, ‖w n‖) * ‖x‖ := by
  exact (weightedShiftCLM w hw).le_opNorm x |>.trans_eq (by rw [norm_weightedShiftCLM])

/-- **Norm bound for the weighted backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$, and let
$B_w$ be the weighted backward shift on $\ell^2(\mathbb{N}, \mathbb{K})$, given by
$(B_w x)_i = \overline{w_i}\, x_{i+1}$. Then $\|B_w x\| \le (\sup_n |w_n|)\, \|x\|$ for every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem norm_weightedBackwardLinMap_apply_le {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) :
    ‖weightedBackwardLinMap w hw x‖ ≤ (⨆ n, ‖w n‖) * ‖x‖ := by
  exact (weightedBackwardCLM w hw).le_opNorm x |>.trans_eq (by rw [norm_weightedBackwardCLM])

/-- **The weighted backward shift after the forward shift is diagonal.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$,
and on $\ell^2(\mathbb{N}, \mathbb{K})$ let $S_w$ be the weighted forward shift,
$(S_w x)_0 = 0$ and $(S_w x)_{n+1} = w_n x_n$, and $B_w$ the weighted backward shift,
$(B_w x)_i = \overline{w_i}\, x_{i+1}$. Then $(B_w S_w x)_i = |w_i|^2 x_i$ for every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$. -/
theorem backward_comp_shift_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (weightedBackwardCLM w hw ∘L weightedShiftCLM w hw) x i =
      (‖w i‖ ^ 2 : 𝕜) * (x : ℕ → 𝕜) i := by
  rw [ContinuousLinearMap.comp_apply, weightedBackwardCLM_apply,
    weightedBackwardFun_apply, weightedShiftCLM_apply, weightedShiftFun_succ,
    ← mul_assoc, RCLike.conj_mul]

/-- **Forward-after-backward weighted shift is diagonal.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded moduli, and let $S_w$ and
$B_w$ be the weighted forward and backward shifts on $\ell^2(\mathbb{N}, \mathbb{K})$. For every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$, the composite $S_w B_w$ satisfies $(S_w B_w x)_0 = 0$ and
$(S_w B_w x)_i = |w_{i-1}|^2 x_i$ for every $i \ge 1$. -/
theorem shift_comp_backward_apply (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (weightedShiftCLM w hw ∘L weightedBackwardCLM w hw) x i =
      if i = 0 then 0 else (‖w (i - 1)‖ ^ 2 : 𝕜) * (x : ℕ → 𝕜) i := by
  cases i with
  | zero => simp [weightedShiftCLM_apply]
  | succ n => simp [weightedShiftCLM_apply, weightedBackwardCLM_apply,
      ← mul_assoc, RCLike.mul_conj]

/-- **The weighted backward shift is a left inverse for unimodular weights.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a sequence in $\mathbb{K}$ with
$|w_n| = 1$ for every $n$. On $\ell^2(\mathbb{N}, \mathbb{K})$ let $S_w$ be the weighted forward
shift, $(S_w x)_0 = 0$ and $(S_w x)_{n+1} = w_n x_n$, and $B_w$ the weighted backward shift,
$(B_w x)_i = \overline{w_i}\, x_{i+1}$. Then $B_w S_w$ is the identity operator. -/
theorem backward_comp_shift_eq_one (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, ‖w n‖ = 1) :
    weightedBackwardCLM w hw ∘L weightedShiftCLM w hw =
      (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rw [backward_comp_shift_apply, h]
  simp

/-- **Weighted shifts with nonzero weights are injective.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$ with
$w_n \neq 0$ for every $n$. Then the weighted forward shift $S_w$ on
$\ell^2(\mathbb{N}, \mathbb{K})$, given by $(S_w x)_0 = 0$ and $(S_w x)_{n+1} = w_n x_n$, is
injective.

The coordinates of $x$ are recovered from $S_w x$ one by one: $x_n = (S_w x)_{n+1} / w_n$. -/
theorem injective_weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, w n ≠ 0) :
    Function.Injective (weightedShiftCLM w hw) := by
  intro a b hab; apply lp.ext; funext i
  have h2 := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hab) (i + 1)
  simp only [weightedShiftCLM_apply, weightedShiftFun_succ] at h2
  exact mul_left_cancel₀ (h i) h2

/-- **A vanishing weight makes the weighted shift non-injective.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and let $w : \mathbb{N} \to \mathbb{K}$ be weights with bounded
moduli. If $w_n = 0$ for some $n$, then the weighted forward shift $S_w$ on
$\ell^2(\mathbb{N}, \mathbb{K})$ is not injective.

Indeed, $S_w$ sends the $n$-th standard basis vector to $0$. -/
theorem not_injective_weightedShiftCLM (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (n : ℕ) (hn : w n = 0) :
    ¬ Function.Injective (weightedShiftCLM w hw) := by
  intro hinj
  have h0 : weightedShiftCLM w hw (lp.single 2 n (1 : 𝕜)) = 0 := by
    rw [weightedShiftCLM_single, hn]; simp
  have hne : (lp.single 2 n (1 : 𝕜) : ℓ²(ℕ, 𝕜)) ≠ 0 := by
    intro h; have := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) h) n; simp at this
  exact hne (hinj (by rw [h0, map_zero]))

/-- **Weighted shifts with unimodular weights preserve norms.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $(w_n)_{n \in \mathbb{N}}$ be a sequence in $\mathbb{K}$ with $|w_n| = 1$ for
every $n$. Then the weighted forward shift $S_w$ on $\ell^2(\mathbb{N}, \mathbb{K})$, given by
$(S_w x)_0 = 0$ and $(S_w x)_{n+1} = w_n x_n$, satisfies $\|S_w x\| = \|x\|$ for every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem norm_weightedShiftCLM_apply_of_forall_norm_eq_one (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (h : ∀ n, ‖w n‖ = 1)
    (x : ℓ²(ℕ, 𝕜)) : ‖weightedShiftCLM w hw x‖ = ‖x‖ := by
  have hS : ‖weightedShiftCLM w hw‖ = 1 := by
    rw [norm_weightedShiftCLM]
    simp [h]
  have hB : ‖weightedBackwardCLM w hw‖ = 1 := by
    rw [norm_weightedBackwardCLM]
    simp [h]
  apply le_antisymm
  · exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [hS, one_mul])
  · have hx := ContinuousLinearMap.le_opNorm (weightedBackwardCLM w hw)
        (weightedShiftCLM w hw x)
    rw [← ContinuousLinearMap.comp_apply, backward_comp_shift_eq_one w hw h,
      one_apply_eq_self, hB, one_mul] at hx
    exact hx

/-- **Isometric weighted shifts.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$(w_n)_{n \in \mathbb{N}}$ be a bounded sequence in $\mathbb{K}$. The weighted forward shift
$S_w$ on $\ell^2(\mathbb{N}, \mathbb{K})$, given by $(S_w x)_0 = 0$ and
$(S_w x)_{n+1} = w_n x_n$, is an isometry if and only if $|w_n| = 1$ for every $n$. -/
theorem isometry_weightedShiftCLM_iff (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    Isometry (weightedShiftCLM w hw) ↔ ∀ n, ‖w n‖ = 1 := by
  constructor
  · intro h n
    have h1 := (isometry_iff_dist_eq.mp h) (lp.single 2 n (1 : 𝕜)) 0
    rw [map_zero, dist_zero_right, dist_zero_right, weightedShiftCLM_single,
      lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one] at h1
    exact h1
  · intro h; rw [isometry_iff_dist_eq]; intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub,
      norm_weightedShiftCLM_apply_of_forall_norm_eq_one w hw h]

/-- **The weighted forward shift with unit weights is the unilateral shift.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$. The weighted forward shift operator on
$\ell^2(\mathbb{N}, \mathbb{K})$ whose weights are all equal to $1$ is the unilateral forward
shift on $\ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem weightedShiftCLM_one {𝕜 : Type*} [RCLike 𝕜]
    (hw : BddAbove (Set.range fun _ : ℕ => ‖(1 : 𝕜)‖)) :
    weightedShiftCLM (fun _ : ℕ => (1 : 𝕜)) hw = LpShiftOperator.shiftCLM := by
  ext x i; cases i <;> simp [weightedShiftCLM_apply, LpShiftOperator.shiftCLM_apply]

/-- **Unit weights give the plain backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. With every weight equal to $1$, the weighted backward shift on
$\ell^2(\mathbb{N}, \mathbb{K})$ is the canonical backward shift. -/
theorem weightedBackwardCLM_one {𝕜 : Type*} [RCLike 𝕜]
    (hw : BddAbove (Set.range fun _ : ℕ => ‖(1 : 𝕜)‖)) :
    weightedBackwardCLM (fun _ : ℕ => (1 : 𝕜)) hw = LpShiftOperator.backwardCLM := by
  ext x i; simp [weightedBackwardCLM_apply, LpShiftOperator.backwardCLM_apply]

end MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator
