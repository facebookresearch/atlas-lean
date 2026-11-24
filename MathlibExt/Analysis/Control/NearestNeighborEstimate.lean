/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Nearest-neighbor estimation for feedback

The estimate uses only recorded transitions. See L. Guo, *Exploring the capability and limits of
the feedback mechanism*, Proc. ICM 2002, Vol. III, [arXiv:math/0305011v1], Remark 4.1.

[arXiv:math/0305011v1]: https://arxiv.org/abs/math/0305011v1
-/

@[expose] public section

namespace MathlibExt.Analysis.Control

/-- **Nearest-neighbor estimate from past transitions.** At time `t = n + 1`, let `y` contain
observations through `t` and `u` controls through `t - 1`. Among indices `i < t`, minimize
`|y_t - y_i|`, taking the least index in a tie (a convention left unspecified in Guo's
Remark 4.1). The estimate is `y_{i+1} - u_i`; the successor observation is already recorded. -/
noncomputable def nearestNeighborEstimate {n : ℕ} (y : Fin (n + 2) → ℝ)
    (u : Fin (n + 1) → ℝ) : ℝ :=
  let key (i : Fin (n + 1)) : ℝ ×ₗ Fin (n + 1) := toLex (|y (Fin.last (n + 1)) - y i.castSucc|, i)
  let i := (ofLex ((Finset.univ.image key).min' (Finset.univ_nonempty.image key))).2
  y i.succ - u i

end MathlibExt.Analysis.Control
