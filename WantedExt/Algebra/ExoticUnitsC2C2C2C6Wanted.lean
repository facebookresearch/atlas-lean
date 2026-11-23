/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Exotic units in the integral group ring of C₂ × C₂ × C₂ × C₆

`OWR-11129-005` (Computational Group Theory (2012)): does the integral
group ring `ℤG` of `G = C₂ × C₂ × C₂ × C₆` contain a unit that is not
of the trivial form `±g`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted

/-- **The group $C_2 \times C_2 \times C_2 \times C_6$.** The abelian group
$G = C_2 \times C_2 \times C_2 \times C_6$, the product of cyclic groups of orders $2$, $2$, $2$
and $6$, written additively as
$\mathbb{Z}/2 \times \mathbb{Z}/2 \times \mathbb{Z}/2 \times \mathbb{Z}/6$.

Source: `OWR-11129-005` (Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37). -/
abbrev OWRGroup : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 6

/-- **The integral group ring of $C_2 \times C_2 \times C_2 \times C_6$.** The integral group
ring $\mathbb{Z}G$ of $G = C_2 \times C_2 \times C_2 \times C_6$: finitely supported formal
$\mathbb{Z}$-linear combinations of elements of $G$, with the product extending the group
operation of $G$ bilinearly.

Source: `OWR-11129-005` (Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37). -/
abbrev OWRGroupRing : Type := AddMonoidAlgebra ℤ OWRGroup

/-- **Exotic unit conjecture for $C_2 \times C_2 \times C_2 \times C_6$.** Let
$G = C_2 \times C_2 \times C_2 \times C_6$. The statement that the integral group ring
$\mathbb{Z}G$ contains an exotic unit: a unit $u$ with $u \ne g$ and $u \ne -g$ for every
$g \in G$.

Source: the open question of `OWR-11129-005` (Computational Group Theory (2012),
Oberwolfach Reports, DOI 10.4171/owr/2011/37). -/
def conjecture : Prop :=
  ∃ u : OWRGroupRingˣ, ∀ g : OWRGroup, ∀ s : ℤˣ,
    (↑u : OWRGroupRing) ≠ AddMonoidAlgebra.single g (↑s : ℤ)

/--
**No exotic units in the integral group ring of $C_2 \times C_2 \times C_2 \times C_6$.** Let
$G = C_2 \times C_2 \times C_2 \times C_6$. Every unit $u$ of the integral group ring
$\mathbb{Z}G$ is trivial: $u = g$ or $u = -g$ for some $g \in G$.

Classical: G. Higman (1940) showed the integral group ring of an abelian group
of exponent dividing 4 or 6 has only the units $\pm g$. Via the cut-group criterion in Bächle
(arXiv:1701.04347, Prop. 2.2), $C_2^3 \times C_6$ (exponent 6) is an abelian cut group, so every
unit of $\mathbb{Z}G$ is trivial and no exotic unit exists.

Source: Andreas Bächle, Integral group rings of solvable groups with trivial central units,
Forum Math. 30 (2018), arXiv:1701.04347, https://arxiv.org/abs/1701.04347. Moved from
`OpenConjectures/Algebra/ExoticUnitsC2C2C2C6`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted
