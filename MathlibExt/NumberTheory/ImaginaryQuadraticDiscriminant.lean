/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic

set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/

namespace ImaginaryQuadraticDiscriminant

@[expose] public section

/-- **Imaginary quadratic discriminant.** An integer $D$ is an imaginary quadratic discriminant
if $D < 0$ and either $D \equiv 0 \pmod 4$ or $D \equiv 1 \pmod 4$. -/
def IsImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- **Fundamental imaginary quadratic discriminant.** An integer $D$ is a fundamental imaginary
quadratic discriminant if $D < 0$ and $D$ is a fundamental discriminant. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D

/-- **Imaginary quadratic discriminants.** The set of imaginary quadratic discriminants is the set
of integers $D$ such that $D < 0$ and $D$ is congruent to $0$ or $1$ modulo $4$. -/
def imaginaryQuadraticDiscriminants : Set Int :=
  {D | IsImaginaryQuadraticDiscriminant D}

/-- **Fundamental imaginary quadratic discriminants.** The set of fundamental imaginary quadratic
discriminants is the set of integers $D$ with $D < 0$ that are fundamental discriminants. -/
def fundamentalImaginaryQuadraticDiscriminants : Set Int :=
  {D | IsFundamentalImaginaryQuadraticDiscriminant D}

@[simp]
theorem mem_imaginaryQuadraticDiscriminants {D : Int} :
    D ∈ imaginaryQuadraticDiscriminants ↔ IsImaginaryQuadraticDiscriminant D :=
  Iff.rfl

@[simp]
theorem mem_fundamentalImaginaryQuadraticDiscriminants {D : Int} :
    D ∈ fundamentalImaginaryQuadraticDiscriminants ↔
      IsFundamentalImaginaryQuadraticDiscriminant D :=
  Iff.rfl

/-- **Conductor decomposition of an imaginary quadratic discriminant.** For an integer $D$, a
decomposition of $D$ consists of integers $u$ and $D_K$ such that $u \ge 1$, $D_K$ is a
fundamental imaginary quadratic discriminant, and $D = u^2 D_K$. The integer $u$ is called the
conductor. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : Int) where
  u : Int
  D_K : Int
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

/-- **Characterization of imaginary quadratic discriminants.** An integer $D$ is an imaginary
quadratic discriminant if and only if $D < 0$ and $D$ is congruent to $0$ or $1$ modulo $4$. -/
theorem isImaginaryQuadraticDiscriminant_iff (D : Int) :
    IsImaginaryQuadraticDiscriminant D ↔ D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1) :=
  Iff.rfl

/-- **Criterion for an imaginary quadratic discriminant.** If an integer $D$ satisfies $D < 0$
and either $D \equiv 0 \pmod 4$ or $D \equiv 1 \pmod 4$, then $D$ is an imaginary quadratic
discriminant. -/
theorem isImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 0 ∨ D % 4 = 1) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hmod⟩

/-- **Imaginary quadratic discriminants are negative.** Every imaginary quadratic discriminant
$D$ satisfies $D < 0$. -/
theorem isImaginaryQuadraticDiscriminant_neg {D : Int}
    (h : IsImaginaryQuadraticDiscriminant D) : D < 0 :=
  h.1

/-- **Imaginary quadratic discriminants are congruent to 0 or 1 mod 4.** Every imaginary
quadratic discriminant $D$ satisfies $D \equiv 0 \pmod 4$ or $D \equiv 1 \pmod 4$. -/
theorem isImaginaryQuadraticDiscriminant_mod {D : Int}
    (h : IsImaginaryQuadraticDiscriminant D) : D % 4 = 0 ∨ D % 4 = 1 :=
  h.2

/-- **Negative multiples of 4 are imaginary quadratic discriminants.** If an integer $D$
satisfies $D < 0$ and $D \equiv 0 \pmod 4$, then $D$ is an imaginary quadratic
discriminant. -/
theorem isImaginaryQuadraticDiscriminant_of_mod_zero {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 0) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, Or.inl hmod⟩

/-- **Negative integers congruent to 1 mod 4 are imaginary quadratic discriminants.** If an
integer $D$ satisfies $D < 0$ and $D \equiv 1 \pmod 4$, then $D$ is an imaginary quadratic
discriminant. -/
theorem isImaginaryQuadraticDiscriminant_of_mod_one {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 1) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, Or.inr hmod⟩

/-- **Characterization of fundamental imaginary quadratic discriminants.** An integer $D$ is a
fundamental imaginary quadratic discriminant if and only if $D < 0$ and $D$ is a fundamental
discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_iff (D : Int) :
    IsFundamentalImaginaryQuadraticDiscriminant D ↔
      D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D :=
  Iff.rfl

/-- **Negative fundamental discriminants are fundamental imaginary quadratic discriminants.** If
an integer $D$ satisfies $D < 0$ and is a fundamental discriminant, then $D$ is a fundamental
imaginary quadratic discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hfund : MetaMathlibExt.IsFundamentalDiscriminant D) :
    IsFundamentalImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hfund⟩

/-- **Fundamental imaginary quadratic discriminants are fundamental discriminants.** Every
fundamental imaginary quadratic discriminant $D$ is a fundamental discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant {D : Int}
    (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
    MetaMathlibExt.IsFundamentalDiscriminant D :=
  h.2

/-- Every fundamental imaginary quadratic discriminant is an imaginary quadratic
discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_isImaginary {D : Int}
    (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
    IsImaginaryQuadraticDiscriminant D := by
  obtain ⟨hneg, hfund⟩ := h
  unfold MetaMathlibExt.IsFundamentalDiscriminant at hfund
  rcases hfund with ⟨_, hmod1⟩ | ⟨m, hDm, _, _⟩
  · exact ⟨hneg, Or.inr hmod1⟩
  · have h0 : D % 4 = 0 := by simp [hDm]
    exact ⟨hneg, Or.inl h0⟩

namespace ImaginaryQuadraticDiscriminantDecomposition

variable {D : Int}

/-- **The fundamental part of a conductor decomposition.** For every conductor decomposition of
an integer $D$, consisting of an integer $u \ge 1$ and a fundamental imaginary quadratic
discriminant $D_K$ with $D = u^2 D_K$, the integer $D_K$ is a fundamental imaginary quadratic
discriminant. -/
theorem isFundamental (h : ImaginaryQuadraticDiscriminantDecomposition D) :
    IsFundamentalImaginaryQuadraticDiscriminant h.D_K :=
  h.hD_K

/-- **The conductor of a discriminant decomposition is at least one.** For every decomposition of
an integer $D$ into a conductor $u$ and a fundamental imaginary quadratic discriminant $D_K$,
we have $u \ge 1$. -/
theorem u_ge_one (h : ImaginaryQuadraticDiscriminantDecomposition D) : h.u ≥ 1 :=
  h.hu

/-- **The equation of a discriminant decomposition.** For every decomposition of an integer $D$
into a conductor $u$ and a fundamental imaginary quadratic discriminant $D_K$, we have
$D = u^2 D_K$. -/
theorem prop_eq (h : ImaginaryQuadraticDiscriminantDecomposition D) :
    D = h.u ^ 2 * h.D_K :=
  h.hD

/-- **Decomposition from a conductor and a fundamental discriminant.** Let $D$ be an integer. If
$u \ge 1$ is an integer, $D_K$ is a fundamental imaginary quadratic discriminant and
$D = u^2 D_K$, then $u$ and $D_K$ form a decomposition of $D$ into the conductor $u$ and the
fundamental imaginary quadratic discriminant $D_K$. -/
def ofFundamental (u D_K : Int) (hu : u ≥ 1)
    (hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K)
    (hD : D = u ^ 2 * D_K) : ImaginaryQuadraticDiscriminantDecomposition D :=
  ⟨u, D_K, hu, hD_K, hD⟩

end ImaginaryQuadraticDiscriminantDecomposition

end

end ImaginaryQuadraticDiscriminant
