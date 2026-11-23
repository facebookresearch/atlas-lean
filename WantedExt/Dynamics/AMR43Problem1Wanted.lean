/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 43, Problem 1: Hochman aperiodic conjugacy question
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.SymbolicDynamics.FullShift

@[expose] public section

namespace MathlibExt.Dynamics.AMR43Problem1Wanted

open SymbolicDynamics.FullShift

/-! Source record `AMR-043-0001__4400001`. -/

/-- **The full 2-shift.** $X$ is the space of all two-sided sequences
$x = (x_i)_{i \in \mathbb{Z}}$ with every $x_i \in \{0, 1\}$, carrying the product topology.

Source: [AMR-043-0001]. -/
abbrev X : Type := FullShiftSpace 2

/-- **The full 3-shift.** The space of all two-sided sequences $y = (y_i)_{i \in \mathbb{Z}}$
with every $y_i \in \{0, 1, 2\}$, carrying the product topology. It is the ambient space of the
proper 3-colouring shift.

Source: [AMR-043-0001]. -/
abbrev YAmb : Type := FullShiftSpace 3

/-- **The proper 3-colouring shift.** $Y$ is the set of sequences $y = (y_i)_{i \in \mathbb{Z}}$
in the full 3-shift (so every $y_i \in \{0, 1, 2\}$) such that $y_i \ne y_{i+1}$ for every
$i \in \mathbb{Z}$.

It is a mixing shift of finite type.

Source: [AMR-043-0001]. -/
def Y : Set YAmb := { y | ∀ i : ℤ, y i ≠ y (i + 1) }

/-- **Aperiodic part of the full 2-shift.** Let $\sigma$ be the left shift on the full 2-shift
$X$, given by $(\sigma x)_i = x_{i+1}$. The aperiodic part of $X$ is the set of all $x \in X$
that are not periodic for $\sigma$, that is, with $\sigma^n x \ne x$ for every $n \ge 1$.

Source: [AMR-043-0001]. -/
def AperiodicX : Set X := (Function.periodicPts (unitShift 2))ᶜ

/-- **Aperiodic part of the 3-colouring shift.** Let $\sigma$ be the left shift on the full
3-shift, given by $(\sigma y)_i = y_{i+1}$. The aperiodic part of the proper 3-colouring shift
$Y$ is the set of all $y \in Y$ that are not periodic for $\sigma$, that is, with
$\sigma^n y \ne y$ for every $n \ge 1$.

Source: [AMR-043-0001]. -/
def AperiodicY : Set YAmb := Y \ Function.periodicPts (unitShift 3)

private theorem unitShift_mem_periodicPts_iff {N : ℕ} (x : FullShiftSpace N) :
    unitShift N x ∈ Function.periodicPts (unitShift N) ↔
      x ∈ Function.periodicPts (unitShift N) := by
  constructor
  · rintro ⟨n, hn, hper⟩
    refine ⟨n, hn, ?_⟩
    apply (shiftHomeomorph N).injective
    change unitShift N ((unitShift N)^[n] x) = unitShift N x
    rw [(Function.Commute.self_iterate (unitShift N) n).eq]
    exact hper
  · rintro ⟨n, hn, hper⟩
    exact ⟨n, hn, hper.apply⟩

/-- **Shift on the aperiodic part of the full 2-shift.** The left shift $\sigma$, given by
$(\sigma x)_i = x_{i+1}$, maps the aperiodic part of the full 2-shift $X$ into itself; this is
the self-map of the aperiodic part of $X$ obtained by restricting $\sigma$ to it.

Source: [AMR-043-0001]. -/
def shiftXRes (a : ↥AperiodicX) : ↥AperiodicX :=
  ⟨unitShift 2 a, by
    exact fun h ↦ a.property
      ((unitShift_mem_periodicPts_iff (N := 2) (a : X)).mp h)⟩

/-- **Shift on the aperiodic part of the 3-colouring shift.** The left shift $\sigma$, given by
$(\sigma y)_i = y_{i+1}$, maps the aperiodic part of the proper 3-colouring shift $Y$ into
itself; this is the self-map of the aperiodic part of $Y$ obtained by restricting $\sigma$
to it.

Source: [AMR-043-0001]. -/
def shiftYRes (a : ↥AperiodicY) : ↥AperiodicY :=
  ⟨unitShift 3 a, by
    have ha : (a : YAmb) ∈ Y ∧ (a : YAmb) ∉ Function.periodicPts (unitShift 3) :=
      a.property
    constructor
    · change ∀ i : ℤ, unitShift 3 (a : YAmb) i ≠ unitShift 3 (a : YAmb) (i + 1)
      intro i
      simpa [unitShift_apply, add_assoc, add_comm, add_left_comm] using ha.1 (1 + i)
    · exact fun h ↦ ha.2
        ((unitShift_mem_periodicPts_iff (N := 3) (a : YAmb)).mp h)⟩

/-- **Hochman's aperiodic conjugacy question.** Let $X$ be the full 2-shift and $Y$ the proper
3-colouring shift, write $X \setminus \mathrm{Per}(X)$ and $Y \setminus \mathrm{Per}(Y)$ for
their aperiodic parts with the subspace topologies, and let $\sigma$ be the left shift
$(\sigma z)_i = z_{i+1}$ on each. The statement is that there is a homeomorphism
$e \colon X \setminus \mathrm{Per}(X) \to Y \setminus \mathrm{Per}(Y)$ with
$e(\sigma a) = \sigma(e(a))$ for every $a \in X \setminus \mathrm{Per}(X)$, that is, the two
aperiodic parts are topologically conjugate.

Source: [AMR-043-0001] Hochman problem 1. -/
def conjecture : Prop :=
  ∃ e : Homeomorph ↥AperiodicX ↥AperiodicY,
    ∀ a : ↥AperiodicX, e (shiftXRes a) = shiftYRes (e a)

/--
**The aperiodic parts of the full 2-shift and the 3-colouring shift are not conjugate.**
Let $X$ be the full 2-shift, $Y$ the proper 3-colouring shift, and $\sigma$ the left shift on
each. There is no homeomorphism $e$ from the aperiodic part of $X$ onto the aperiodic part of
$Y$, each with the subspace topology, such that $e(\sigma a) = \sigma(e(a))$ for every $a$ in the
aperiodic part of $X$; that is, Hochman's aperiodic conjugacy question has a negative answer.

Salo proves that every conjugacy between infinite transitive shifts of finite type minus
periodic points extends to a conjugacy of the shifts of finite type; since the full 2-shift
has fixed points and the proper 3-colouring shift has none, the aperiodic parts are not
conjugate.

Source: Ville Salo, Conjugacy of transitive SFTs minus
periodic points, Proc. London Math. Soc. (accepted; arXiv v3 2023), arXiv:2104.09860,
https://arxiv.org/abs/2104.09860. Moved from `OpenConjectures/Dynamics/AMR43Problem1`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Dynamics.AMR43Problem1Wanted
