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

public import MathlibExt.Topology.Algebra.Module.Matrix
public import MathlibExt.Analysis.Normed.Operator.Compact.Pi

/-!
# Compactness of rectangular operator matrices

Let `R` be a semiring and `E,F` topological spaces with additive-group and `R`-module
structures. For operators between the product-topological `PiLp` carriers, each matrix entry of
a compact operator is compact, with no finiteness assumption on its indices.

For finite rows and columns, and continuous addition on `F`, the matrix column action is compact
exactly when every entry is compact. No norms, completeness, separation or scalar-action
continuity are assumed. These are product topologies, not infinite square-summable Hilbert
topologies.
-/

public section

open scoped BigOperators

universe uR uM uN uE uF

variable {R : Type uR} [Semiring R]
variable {m : Type uM} {n : Type uN}
variable {E : Type uE} {F : Type uF}
variable [AddCommGroup E] [TopologicalSpace E] [Module R E]
variable [AddCommGroup F] [TopologicalSpace F] [Module R F]

/-- **Compact coordinate entry of a rectangular product operator.** Let `R` be a semiring and
`E,F` additive commutative groups with topologies and `R`-module structures. Let `m,n` be
index types; the carriers `PiLp 2 (fun _ : n => E)` and `PiLp 2 (fun _ : m => F)` have
their product topologies. assume decidable equality on `n`. If `T : PiLp(E^n) →L[R]
PiLp(F^m)` is compact, every recovered entry `T.toPiLpMatrix i j : E →L[R] F` is compact.
Indices may be infinite and addition on `F` need not be continuous. -/
theorem IsCompactOperator.toPiLpMatrix [DecidableEq n]
    {T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)}
    (hT : IsCompactOperator T) (i : m) (j : n) :
    IsCompactOperator (T.toPiLpMatrix i j) := by
  let J : E →L[R] PiLp 2 (fun _ : n => E) :=
    (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single R (fun _ : n => E) j)
  let P : PiLp 2 (fun _ : m => F) →L[R] F :=
    (ContinuousLinearMap.proj i : (m → F) →L[R] F).comp
      (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).toContinuousLinearMap
  have hEntry : T.toPiLpMatrix i j = P.comp (T.comp J) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.toPiLpMatrix_apply]
    rfl
  rw [hEntry]
  exact (hT.comp_clm J).clm_comp P

/-- **Compact finite matrix action exactly when all entries are compact.** Let `R` be a
semiring and `E,F` additive commutative groups with topologies and `R`-module structures.
Let `m,n` be index types; the carriers `PiLp 2 (fun _ : n => E)` and `PiLp 2 (fun _ : m =>
F)` have their product topologies. assume `m` is finite, `n` has a finite enumeration, and
addition on `F` is continuous. For `M : Matrix m n (E →L[R] F)`, its column operator is
compact exactly when each `M i j` is compact. -/
theorem Matrix.isCompactOperator_toPiLpContinuousLinearMap_iff [Finite m] [Fintype n]
    [ContinuousAdd F] (M : Matrix m n (E →L[R] F)) :
    IsCompactOperator M.toPiLpContinuousLinearMap ↔
      ∀ (i : m) (j : n), IsCompactOperator (M i j) := by
  classical
  constructor
  · intro hM i j
    simpa only [ContinuousLinearMap.toPiLpMatrix_toPiLpContinuousLinearMap] using
      (hM.toPiLpMatrix i j)
  · intro hEntries
    let P (j : n) : PiLp 2 (fun _ : n => E) →L[R] E :=
      (ContinuousLinearMap.proj j : (n → E) →L[R] E).comp
        (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).toContinuousLinearMap
    have hRows (i : m) : IsCompactOperator
        (fun v : PiLp 2 (fun _ : n => E) => ∑ j : n, M i j (v j)) := by
      have hFactors (j : n) : IsCompactOperator
          (fun v : PiLp 2 (fun _ : n => E) => M i j (v j)) := by
        change IsCompactOperator ((M i j) ∘ P j)
        exact (hEntries i j).comp_clm (P j)
      have hSum : IsCompactOperator
          (∑ j : n, (fun v : PiLp 2 (fun _ : n => E) => M i j (v j))) := by
        refine Finset.sum_induction (s := Finset.univ)
          (fun j : n => fun v : PiLp 2 (fun _ : n => E) => M i j (v j))
          (fun f : PiLp 2 (fun _ : n => E) → F => IsCompactOperator f)
          ?_ ?_ (fun j _ => hFactors j)
        · intro f g hf hg
          exact hf.add hg
        · exact isCompactOperator_zero
      simpa only [Finset.sum_fn] using hSum
    have hProduct : IsCompactOperator
        (fun v : PiLp 2 (fun _ : n => E) => WithLp.ofLp (M.toPiLpContinuousLinearMap v)) := by
      apply (isCompactOperator_pi_iff _).mpr
      intro i
      change IsCompactOperator
        (fun v : PiLp 2 (fun _ : n => E) => M.toPiLpContinuousLinearMap v i)
      simpa only [Matrix.toPiLpContinuousLinearMap_apply] using hRows i
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using
      (hProduct.continuous_comp (PiLp.continuous_toLp 2 (fun _ : m => F)))

/-- **Compactness detected by finite rectangular entries.** Let `R` be a semiring and `E,F`
additive commutative groups with topologies and `R`-module structures. Let `m,n` be index
types; the carriers `PiLp 2 (fun _ : n => E)` and `PiLp 2 (fun _ : m => F)` have their
product topologies. assume `m,n` are finite, equality on `n` is decidable, and addition on
`F` is continuous. An operator `T : PiLp(E^n) →L[R] PiLp(F^m)` is compact exactly when
every recovered matrix entry `T.toPiLpMatrix i j` is compact. -/
theorem ContinuousLinearMap.isCompactOperator_iff_toPiLpMatrix
    [Finite m] [Finite n] [DecidableEq n] [ContinuousAdd F]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)) :
    IsCompactOperator T ↔ ∀ (i : m) (j : n), IsCompactOperator (T.toPiLpMatrix i j) := by
  constructor
  · intro hT i j
    exact hT.toPiLpMatrix i j
  · intro hEntries
    let : Fintype n := Fintype.ofFinite n
    have hAction : IsCompactOperator T.toPiLpMatrix.toPiLpContinuousLinearMap :=
      (Matrix.isCompactOperator_toPiLpContinuousLinearMap_iff T.toPiLpMatrix).mpr hEntries
    simpa only [Matrix.toPiLpContinuousLinearMap_toPiLpMatrix] using hAction
