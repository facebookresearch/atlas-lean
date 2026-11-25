/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.Torsion

namespace MetaMathlibExt

@[expose] public section

open scoped WeierstrassCurve.Affine

/-- **Mazur's torsion theorem.** Let $E$ be an elliptic curve over $\mathbb{Q}$. The torsion
subgroup of the group $E(\mathbb{Q})$ of rational points of $E$ is finite and has at most $16$
elements.

Only this bound is stated, not Mazur's full list of the fifteen possible torsion subgroups.

Source: B. Mazur, *Modular curves and the Eisenstein ideal*,
Publ. Math. IHÉS 47 (1977), 33–186, doi:10.1007/BF02684339,
<https://www.numdam.org/item/?id=PMIHES_1977__47__33_0>. -/
theorem_wanted mazur_torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite ∧
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16

end

end MetaMathlibExt
