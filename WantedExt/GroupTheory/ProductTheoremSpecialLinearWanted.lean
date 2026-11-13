/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- The **product theorem** for special linear groups: a normalized symmetric generating set of
`SL(n, k)` over a finite field either grows under cubing or is already large.
For every `ε` with `0 < ε < 1` there is `δ > 0` (depending on `n` and `ε`)
such that either `|A|^(1+δ) ≤ |A^3|` or `|SL(n,k)|^(1-ε) ≤ |A|`.

Sources: S. Machado, *Topics in Geometric Group Theory* lecture notes,
<https://sites.google.com/view/simonmachado/teaching>, Theorem 1.9;
originals B. Breuillard, B. Green, T. Tao, *Approximate subgroups of linear
groups*, Geom. Funct. Anal. 21 (2011), and L. Pyber, E. Szabó, *Growth in
finite simple groups of Lie type*, J. Amer. Math. Soc. 29 (2016). -/
theorem_wanted product_theorem_special_linear {n : ℕ} :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (k : Type*) [Field k] [Fintype k] [DecidableEq k]
          (A : Finset (Matrix.SpecialLinearGroup (Fin n) k))
          (_hsymm : A⁻¹ = A)
          (_hone : 1 ∈ A)
          (_hgen : Subgroup.closure (A : Set (Matrix.SpecialLinearGroup (Fin n) k)) = ⊤),
          Real.rpow (Finset.card A : ℝ) (1 + δ)
            ≤ (Finset.card (A ^ 3) : ℝ) ∨
            Real.rpow (Fintype.card (Matrix.SpecialLinearGroup (Fin n) k) : ℝ) (1 - ε)
              ≤ (Finset.card A : ℝ)

end

end MetaMathlibExt
