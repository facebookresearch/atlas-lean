/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Real planar rotation matrices

This file defines the rotation matrix through a real angle `θ`, the real `2 × 2` matrix
`!![cos θ, -sin θ; sin θ, cos θ]`.

Mathlib's `rotation` is a rotation of `ℂ` given by a point of the unit circle, as a linear
isometric equivalence; by `toMatrix_rotation`, its matrix in the basis `1, I` is given by
`Matrix.planeConformalMatrix`, which lands in `GL (Fin 2) ℝ`. Neither is a function of the angle
with values in real matrices.

## Main definitions

- `MetaMathlibExt.Matrix.planarRotation`: the rotation matrix through the angle `θ`.

## References

- J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, *RoFormer: Enhanced Transformer with
  Rotary Position Embedding*, arXiv:2104.09864 (v5), Section 3.2.1, equation (13).
-/

namespace MetaMathlibExt.Matrix

/-- **Real planar rotation matrix.** For $\theta \in \mathbb{R}$, the rotation matrix through the
angle $\theta$ is the real $2 \times 2$ matrix
$R(\theta) = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}$.

Source: J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, *RoFormer: Enhanced Transformer
with Rotary Position Embedding*, arXiv:2104.09864 (v5), Section 3.2.1, equation (13) (the
rotation matrix through the angle $m\theta$). -/
@[expose] public noncomputable def planarRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

end MetaMathlibExt.Matrix
