/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import MathlibExt.NumberTheory.DirichletCharacter.QuadraticCharacterAux

@[expose] public section

namespace MetaMathlibExt

/-- **Decomposition of rational primes in a quadratic field.** Let $K/\mathbb{Q}$ have degree
$2$ and signed discriminant $D$, and let $p$ be a rational prime, including $2$. If the
Kronecker symbol $\left(\frac{D}{p}\right)$ is $0$, then $p\mathcal{O}_K$ is the square of a
nonzero prime ideal of norm $p$. If it is $1$, then $p\mathcal{O}_K$ is the product of two
distinct prime ideals of norm $p$, exchanged by the nontrivial $\mathbb{Q}$-automorphism of
$K$. If it is $-1$, then $p\mathcal{O}_K$ is prime and has norm $p^2$.

Source: F. Keune, *Number Fields* (2023), Theorem 3.7, pp. 52–53,
<https://doi.org/10.54195/IPVU4488>. -/
theorem_wanted quadraticField_prime_decomposition (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    let χ := kroneckerSym (NumberField.discr K) p
    let I : Ideal (NumberField.RingOfIntegers K) := Ideal.span {(p : NumberField.RingOfIntegers K)}
    (χ = 0 → ∃ P : Ideal (NumberField.RingOfIntegers K),
      P ≠ ⊥ ∧ P.IsPrime ∧ I = P ^ 2 ∧ P.absNorm = p) ∧
    (χ = 1 → ∃ (σ : K ≃ₐ[ℚ] K) (P : Ideal (NumberField.RingOfIntegers K)),
      let Q := P.map (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
      σ ≠ AlgEquiv.refl ∧ P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧ I = P * Q ∧
        P.absNorm = p ∧ Q.absNorm = p) ∧
    (χ = -1 → I.IsPrime ∧ I.absNorm = p ^ 2)

end MetaMathlibExt

end
