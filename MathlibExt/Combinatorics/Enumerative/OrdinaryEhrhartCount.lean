/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Card

/-!
# Ordinary Ehrhart counts

This file records the ordinary lattice-point count used by Ryuichi Sakamoto,
*The h*-Polynomial of the Cut Polytope of K_{2,m} in the Lattice Spanned by
its Vertices*, Journal of Integer Sequences 23 (2020), Article 20.7.5.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Ordinary Ehrhart count.** For a natural number $d$, a set $P \subseteq \mathbb{Q}^d$ and a
natural number $m$, the ordinary Ehrhart count is the number $|mP \cap \mathbb{Z}^d|$ of integer
points in the dilate $mP = \{m x : x \in P\}$, where $\mathbb{Z}^d$ is viewed inside
$\mathbb{Q}^d$; it is $0$ when $mP \cap \mathbb{Z}^d$ is infinite.

For polytopes the intersection is finite.

Source: Ryuichi Sakamoto, "The h*-Polynomial of the Cut Polytope of K_{2,m} in the Lattice
Spanned by its Vertices," Journal of Integer Sequences 23 (2020), Article 20.7.5; concept
`jis_sem_91fece955b8d30a79b80296c`, statement `jis_52595824a0e5a66cf10405d1`.
-/
noncomputable def ordinaryEhrhartCount (d : ℕ) (P : Set (Fin d → ℚ)) (m : ℕ) : ℕ :=
  Set.ncard
    (((fun x : Fin d → ℚ => (m : ℚ) • x) '' P) ∩
      Set.range fun z : Fin d → ℤ => fun i => (z i : ℚ))

end

end MetaMathlibExt
