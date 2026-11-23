/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rubel H∞ coherence (AMR 022-5024)
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace MathlibExt.Analysis.RubelHInfinityCoherenceWanted

/-! Source record `AMR-022-5024`, Research Problems in Function Theory,
Problem 5.24 (L. A. Rubel): is the intersection of two finitely generated
ideals in H∞ finitely generated?

H∞ is modeled extensionally on the disc: elements are functions on the
subtype `Disc`, so equality and the ring operations cannot see off-disc
values. Analyticity is witnessed by an ambient function differentiable on
the ball and agreeing on the disc.
-/

/-- **The open unit disc.** The open unit disc
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$, the open ball of radius $1$ about $0$ in
$\mathbb{C}$, taken as a space in its own right whose points are the points of the disc. -/
abbrev Disc : Type := ↥(Metric.ball (0 : ℂ) 1)

/-- **Membership in $H^\infty$ of the unit disc.** A complex-valued function $f$ on the open unit
disc $\mathbb{D}$ belongs to $H^\infty$ when there is a function $F : \mathbb{C} \to \mathbb{C}$
that is complex differentiable on $\mathbb{D}$ and satisfies $f(z) = F(z)$ for every
$z \in \mathbb{D}$, and there is a real number $C \ge 0$ with $|f(z)| \le C$ for every
$z \in \mathbb{D}$.

Source: [AMR-022-5024], Research Problems in Function Theory, Problem 5.24. -/
def IsHInf (f : Disc → ℂ) : Prop :=
  (∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1) ∧
    ∀ z : Disc, f z = F z.val) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Disc, ‖f z‖ ≤ C

/-- **The ring $H^\infty$ as a subring of functions on the disc.** $H^\infty$ is the subring of
the ring of all complex-valued functions on the open unit disc $\mathbb{D}$, under pointwise
addition and multiplication, consisting of the functions that belong to $H^\infty$: those that
agree on $\mathbb{D}$ with a function $\mathbb{C} \to \mathbb{C}$ complex differentiable on
$\mathbb{D}$ and are bounded on $\mathbb{D}$.

Source: [AMR-022-5024], Research Problems in Function Theory, Problem 5.24. -/
def HInfinitySubring : Subring (Disc → ℂ) where
  carrier := {f | IsHInf f}
  zero_mem' := by
    show IsHInf 0
    refine ⟨⟨0, differentiableOn_const _, ?_⟩, 0, le_refl 0, ?_⟩
    · intro z; simp
    · intro z; simp
  one_mem' := by
    show IsHInf 1
    refine ⟨⟨1, differentiableOn_const _, ?_⟩, 1, zero_le_one, ?_⟩
    · intro z; simp
    · intro z; simp
  add_mem' := fun {f g} hf hg => by
    show IsHInf (f + g)
    obtain ⟨⟨F, hFd, hFeq⟩, C1, hC1, hb1⟩ := hf
    obtain ⟨⟨G, hGd, hGeq⟩, C2, hC2, hb2⟩ := hg
    refine ⟨⟨F + G, hFd.add hGd, ?_⟩, C1 + C2, add_nonneg hC1 hC2, ?_⟩
    · intro z
      show (f + g) z = (F + G) z.val
      rw [Pi.add_apply, hFeq z, hGeq z, Pi.add_apply]
    · intro z
      calc ‖(f + g) z‖ = ‖f z + g z‖ := by rw [Pi.add_apply]
        _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
        _ ≤ C1 + C2 := add_le_add (hb1 z) (hb2 z)
  mul_mem' := fun {f g} hf hg => by
    show IsHInf (f * g)
    obtain ⟨⟨F, hFd, hFeq⟩, C1, hC1, hb1⟩ := hf
    obtain ⟨⟨G, hGd, hGeq⟩, C2, hC2, hb2⟩ := hg
    refine ⟨⟨F * G, hFd.mul hGd, ?_⟩, C1 * C2, mul_nonneg hC1 hC2, ?_⟩
    · intro z
      show (f * g) z = (F * G) z.val
      rw [Pi.mul_apply, hFeq z, hGeq z, Pi.mul_apply]
    · intro z
      calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := by rw [Pi.mul_apply, norm_mul]
        _ ≤ C1 * C2 := mul_le_mul (hb1 z) (hb2 z) (norm_nonneg _) hC1
  neg_mem' := fun {f} hf => by
    show IsHInf (-f)
    obtain ⟨⟨F, hFd, hFeq⟩, C, hC, hb⟩ := hf
    refine ⟨⟨-F, hFd.neg, ?_⟩, C, hC, ?_⟩
    · intro z
      show (-f) z = (-F) z.val
      rw [Pi.neg_apply, hFeq z, Pi.neg_apply]
    · intro z
      calc ‖(-f) z‖ = ‖f z‖ := by rw [Pi.neg_apply, norm_neg]
        _ ≤ C := hb z

/-- **Elements of $H^\infty$.** The space whose points are the members of the subring $H^\infty$
of complex-valued functions on the open unit disc $\mathbb{D}$, that is, the bounded functions
on $\mathbb{D}$ that agree on $\mathbb{D}$ with a function complex differentiable there.

Source: [AMR-022-5024], Research Problems in Function Theory, Problem 5.24. -/
def HInfinity : Type := ↥HInfinitySubring

/-- Commutative ring structure on H∞ inherited from its subring construction
([AMR-022-5024], Problem 5.24). -/
instance : CommRing HInfinity :=
  inferInstanceAs (CommRing ↥HInfinitySubring)

/-- **Rubel's problem on intersections of finitely generated ideals in $H^\infty$.** The
statement that for any two finitely generated ideals $I$ and $J$ of the commutative ring
$H^\infty$ of bounded holomorphic functions on the open unit disc, the intersection $I \cap J$ is
finitely generated.

Rubel asked whether this statement is true.

Source: [AMR-022-5024], Research Problems in Function Theory, Problem 5.24 (L. A. Rubel). -/
def RubelProblem524 : Prop :=
  ∀ I J : Ideal HInfinity, I.FG → J.FG → (I ⊓ J).FG

/--
**McVoy–Rubel theorem on finitely generated ideals of $H^\infty$.** For any two finitely
generated ideals $I$ and $J$ of the commutative ring $H^\infty$ of bounded holomorphic functions
on the open unit disc, the intersection $I \cap J$ is finitely generated. This answers Rubel's
Problem 5.24 positively.

Resolved by McVoy and Rubel (J. Funct. Anal. 21 (1976) 76-87), who proved that $H^\infty$ of the
unit disc is a coherent ring. Restated in Mortini, arXiv:1606.05568, and Hayman-Lingham
Update 5.24.

Source: R. Mortini,
Noncoherent uniform algebras in C^n (2016), arXiv:1606.05568, https://arxiv.org/abs/1606.05568.
Moved from `OpenConjectures/Analysis/RubelHInfinityCoherence`.
-/
public theorem_wanted RubelProblem524_holds : RubelProblem524

end MathlibExt.Analysis.RubelHInfinityCoherenceWanted
