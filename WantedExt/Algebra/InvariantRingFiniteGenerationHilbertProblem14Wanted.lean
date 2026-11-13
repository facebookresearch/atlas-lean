/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite generation of rings of invariants (Hilbert's fourteenth problem)

Hilbert's fourteenth problem, in the form of the UnsolvedMath record HIL-014: is the ring of
invariants of a linear algebraic group acting on a polynomial ring always finitely generated?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.Algebra.InvariantRingFiniteGenerationHilbertProblem14Wanted

/-!
Source: D. Hilbert, Mathematical problems (Paris, 1900), Bull. Amer. Math. Soc. 8 (1902), 437-479,
Problem 14, as stated in the UnsolvedMath record HIL-014. UnsolvedMath record UM-00000088
(`HIL-014`), dataset ulamai/UnsolvedMath v1.8.0.

The ground field is `ℂ`. A linear algebraic group acting linearly on `ℂ[x₀, …, x_{n-1}]` is
represented by its image in `GL_n(ℂ)`, a Zariski closed subgroup (`IsAlgebraic`: the invertible
matrices whose entries satisfy a family of polynomial equations); its invariants are the invariants
of the representation. The group acts by linear substitutions, `f(x) ↦ f(g x)`; the convention
`f(g⁻¹ x)` has the same invariants. Finitely generated means generated as a `ℂ`-algebra by finitely
many invariants. Over a finite field the statement would differ: the group of rational points of a
unipotent group is then finite, with finitely generated invariants, which is why the target fixes
`ℂ`.
-/

open MvPolynomial

/-- The linear change of variables `xᵢ ↦ ∑ⱼ gᵢⱼ xⱼ` of `ℂ[x₀, …, x_{n-1}]` given by an invertible
matrix `g`, so that `(linearSubst g f)(x) = f(g x)`. -/
noncomputable def linearSubst {n : ℕ} (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval fun i => ∑ j, C ((g : Matrix (Fin n) (Fin n) ℂ) i j) * X j

/-- `f` is invariant under every element of `G`. -/
def IsInvariant {n : ℕ} (G : Subgroup (GL (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ g ∈ G, linearSubst g f = f

/-- `G` is a linear algebraic group: a Zariski closed subgroup of `GL_n(ℂ)`, the set of invertible
matrices whose entries satisfy some family of polynomial equations. -/
def IsAlgebraic {n : ℕ} (G : Subgroup (GL (Fin n) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n × Fin n) ℂ), ∀ g : GL (Fin n) ℂ,
    g ∈ G ↔ ∀ p ∈ S, eval (fun ij => (g : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2) p = 0

/-- The ring of invariants of `G` is a finitely generated `ℂ`-algebra: finitely many invariants
generate every invariant. -/
def InvariantsFG {n : ℕ} (G : Subgroup (GL (Fin n) ℂ)) : Prop :=
  ∃ s : Finset (MvPolynomial (Fin n) ℂ), (∀ f ∈ s, IsInvariant G f) ∧
    ∀ f, IsInvariant G f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (Fin n) ℂ))

/-- Hilbert's fourteenth problem for linear actions: the ring of invariants of every linear
algebraic group `G ≤ GL_n(ℂ)` acting on `ℂ[x₀, …, x_{n-1}]` by linear substitutions is finitely
generated. -/
def invariantRingsFinitelyGenerated : Prop :=
  ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℂ)), IsAlgebraic G → InvariantsFG G

/--
Resolved false: Nagata gave the first counterexample, a representation of the additive group
`G_a^13` over a field of large transcendence degree (Totaro, introduction; Kuttler and Wallach,
Theorem 1, state it as a linear action of `(F^+)^13` on `F^32`), and Totaro (Theorem 0.1) gives,
over every field and in particular over `ℂ`, explicit linear representations of `G_a^3` on `ℂ^18`,
of `G_a^4` on `ℂ^16` and of `G_a^6` on `ℂ^18` whose rings of invariants are not finitely generated.
The image of such a representation is a Zariski closed subgroup of `GL_n(ℂ)` with the same
invariants. Source: D. Hilbert, Mathematical problems (Paris, 1900), Bull. Amer. Math. Soc. 8
(1902), 437-479, Problem 14, as stated in the UnsolvedMath record HIL-014; resolution: M. Nagata, On
the 14-th problem of Hilbert, Amer. J. Math. 81 (1959), 766-772, https://doi.org/10.2307/2372927; B.
Totaro, Hilbert's 14th problem over finite fields and a conjecture on the cone of curves, Compos.
Math. 144 (2008), 1176-1198, introduction: Nagata's counterexample is a representation of G_a^13
over a field of large transcendence degree (J. Kuttler and N. R. Wallach, arXiv:math/0211245,
Theorem 1: a linear action of (F^+)^13 on F^32 with a ring of invariants that is not finitely
generated); Totaro, Theorem 0.1: over any field k there are explicit linear representations of G_a^3
on A^18, G_a^4 on A^16 and G_a^6 on A^18 whose rings of invariants are not finitely generated,
https://doi.org/10.1112/S0010437X08003667.
-/
public theorem_wanted invariantRingsFinitelyGenerated_refuted : ¬ invariantRingsFinitelyGenerated

end MathlibExt.Algebra.InvariantRingFiniteGenerationHilbertProblem14Wanted
