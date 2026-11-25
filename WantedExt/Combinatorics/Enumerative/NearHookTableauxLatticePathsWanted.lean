/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.NearHookTableauxLatticePaths

/-!
# Near-hook tableaux and first-quadrant lattice paths

The shared definitions and the bijection for $\xi$ are in
`MathlibExt.Combinatorics.Enumerative.NearHookTableauxLatticePaths`.
-/

namespace MetaMathlibExt

/-- **The map $\psi$ is a bijection from near-hook tableaux to first-quadrant paths.** For every
$n \in \mathbb{N}$, the map $\psi$ restricts to a bijection from the standard Young tableaux of
shape $\theta^{(n)}$ onto the set $\mathcal{P}_n$ of first-quadrant paths. Here a standard Young
tableau of shape $\theta^{(n)}$ is a semistandard Young tableau of that shape whose entries map
the $2n + 4$ cells of $\theta^{(n)}$ bijectively onto $\{1, \dots, 2n + 4\}$.

Source: Liam Ayres, Evan Bialo, Alwin Chen, Aidan Cook, Matteus Froese, Erica Liu, Maryam Mohammadi
Yekta, Oliver Pechenik and Benjamin Wong, *An Exceptional Equinumerosity of Lattice Paths and Young
Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Theorem 2
(`jis-2025-25.5.2-thm-2`). -/
public theorem_wanted bijOn_nearHookTableauToPathPsi (n : ℕ) :
    Set.BijOn (nearHookTableauToPathPsi n)
      {T | Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta n).cells
        (Set.Icc 1 (2 * n + 4))}
      (firstQuadrantPaths n)

end MetaMathlibExt
