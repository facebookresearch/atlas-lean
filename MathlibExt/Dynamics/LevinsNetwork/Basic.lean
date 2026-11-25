/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Epidemiology.NextGenerationMatrixBasic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# The Levins metapopulation on a patch network: definitions

On a network of patches `ι` (Hanski and Ovaskainen 2000), patch `i` is occupied with
probability `p i`, an occupied patch `j` sends colonists to patch `i` at rate `C i j ≥ 0`, and
the population of patch `i` goes extinct at rate `e i > 0`:

  `p_i' = (1 - p_i) ∑_j C_ij p_j - e_i p_i`.

The same system is the multi-group SIS model of Lajmanovich and Yorke (1976). This file holds
only the definitions `field`, `IsSolution` and `persistenceNumber`, so that every library may
state results about them. The threshold theory (box invariance, extinction for `R₀ < 1`,
persistence for `R₀ > 1` and irreducible `C`) is in `Domains.Biology.Ecology.LevinsNetwork`.

## References

* I. Hanski and O. Ovaskainen, *The metapopulation capacity of a fragmented landscape*,
  Nature 404 (2000) 755–758.
* A. Lajmanovich and J. A. Yorke, *A deterministic model for gonorrhea in a nonhomogeneous
  population*, Math. Biosci. 28 (1976) 221–236.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.Ecology.LevinsNetwork

open MathlibExt.Biology.Epidemiology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector field of the network Levins model: patch `i` is colonized from the occupied patches
`j` at rates `C i j` when empty (probability `1 - p i`), and goes extinct at rate `e i`,
`p_i' = (1 - p_i) (C p)_i - e_i p_i`. The formula is defined for all real `p`; the probability
reading is for `p ∈ [0, 1]^ι`. -/
def field (C : Matrix ι ι ℝ) (e p : ι → ℝ) : ι → ℝ :=
  fun i => (1 - p i) * (C *ᵥ p) i - e i * p i

/-- `p` solves the network Levins system `p' = field C e p` for all `t ≥ 0` (a two-sided derivative,
also at `t = 0`). -/
structure IsSolution (C : Matrix ι ι ℝ) (e : ι → ℝ) (p : ℝ → ι → ℝ) : Prop where
  /-- Each patch changes by colonization of its empty fraction minus local extinction. -/
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt p (field C e (p t)) t

/-- The **persistence number** `R₀ = ρ(C diag(e)⁻¹)` of the network: the spectral radius of the
next-generation matrix with new colonizations `F = C` and losses `V = diag(e)`. When some `e i = 0`,
`diag(e)` is singular, its inverse is the zero matrix and `R₀ = 0`; with no patches, `R₀ = 0`. -/
noncomputable def persistenceNumber (C : Matrix ι ι ℝ) (e : ι → ℝ) : ℝ :=
  NextGenerationMatrix.R0 C (diagonal e)

end MathlibExt.Biology.Ecology.LevinsNetwork
