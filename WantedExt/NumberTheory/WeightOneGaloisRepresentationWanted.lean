/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Frobenius
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import MathlibExt.NumberTheory.ModularForms.EigenformWith

namespace ModularForm

open CongruenceSubgroup ModularFormClass

open scoped MatrixGroups

/-- **Galois representations attached to weight-one eigenforms (Deligne–Serre).** Let $N \ge 1$,
let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be
a modular form of type $(1, \varepsilon)$ on $\Gamma_0(N)$: a modular form of weight $1$ on
$\Gamma_1(N)$, not necessarily a cusp form, such that

$$f\left(\frac{az+b}{cz+d}\right) = \varepsilon(d)\,(cz+d)\,f(z) \qquad
\text{for all } \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N).$$

Suppose that $f$ is an eigenvector of the Hecke operators $T_p$ for the primes $p \nmid N$, with
eigenvalues $a_p$. Then there is a continuous representation

$$\rho \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to
\operatorname{GL}_2(\mathbb{C})$$

with finite image, unramified at every prime $p \nmid N$, such that

$$\operatorname{Tr} \rho(\operatorname{Frob}_p) = a_p \quad \text{and} \quad
\det \rho(\operatorname{Frob}_p) = \varepsilon(p) \qquad \text{for every prime } p \nmid N.$$

This representation is irreducible if and only if $f$ is a cusp form.

Conventions. Write $f = \sum_{n \ge 0} c_n q^n$ with $q = e^{2\pi i z}$, so that $c_n$ is
`ModularFormClass.qCoeff f n`. The transformation law is hypothesis `hfε`, the condition of
`CuspForm.HasNebentypus` in weight $1$, stated for `f : ModularForm (Gamma1 N) 1` because $f$ need
not be a cusp form. For $p \nmid N$ the operator $T_p$ acts on forms of type $(1, \varepsilon)$ by
$f|T_p = \sum c_{pn} q^n + \varepsilon(p) \sum c_n q^{pn}$, so $f|T_p = a_p f$ says that
$c_{pn} + \varepsilon(p)\,c_{n/p} = a_p\,c_n$ for every $n \ge 0$, where $c_{n/p} = 0$ when
$p \nmid n$: this is hypothesis `ha`. It is imposed only at the primes $p \nmid N$, and $f$ is not
normalized, so $a_p$ is an eigenvalue rather than a coefficient of $f$. `CuspForm.IsEigenformWith`
is defined for cusp forms and is stronger: it also asks for $c_1 = 1$, takes $a_p = c_p$, and
imposes the relations of the operators $U_\ell$ at the primes $\ell \mid N$. Here
$\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`, and its Galois group carries the Krull topology.
Deligne and Serre give $\mathbb{C}$ the discrete topology, so their representations have open
kernel; for a homomorphism from this profinite group that is the same as being continuous for the
usual topology of $\operatorname{GL}_2(\mathbb{C})$ and having finite image, the two properties
asserted. $\overline{\mathbb{Z}}$ is the integral closure of $\mathbb{Z}$ in
$\overline{\mathbb{Q}}$. Unramified at $p$ means that the inertia group of every maximal ideal
$\mathfrak{p}$ of $\overline{\mathbb{Z}}$ over $p$, the elements acting trivially on
$\overline{\mathbb{Z}}/\mathfrak{p}$, acts trivially; these groups are conjugate, so this is the
same as asking it for one $\mathfrak{p}$. $\operatorname{Frob}_p$ is the Frobenius
substitution in Artin's convention, the arithmetic Frobenius, whose inverse is the geometric
Frobenius: any $\sigma$ acting as $x \mapsto x^p$ on $\overline{\mathbb{Z}}/\mathfrak{p}$ for a
maximal ideal $\mathfrak{p}$ over $p$. It is defined up to conjugation and inertia, and the trace
and the determinant are asserted for every such $\sigma$ and $\mathfrak{p}$. Irreducible means that
no line of $\mathbb{C}^2$ is stable under every $\rho(\sigma)$, and $f$ is a cusp form when some
`CuspForm (Gamma1 N) 1` has the same underlying function.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, [Théorème 4.1 and (4.1.1), pp. 513–514](https://doi.org/10.24033/asens.1277),
with modular forms and cusp forms as in §1.2 (p. 508), forms of type $(k, \varepsilon)$ as in §1.5
(p. 509), the operators $T_p$ as in (1.6.1) (p. 509), and linear representations, unramifiedness
and the Frobenius substitution as in §3.1 and Remarque 3.3 (pp. 512–513); the footnote to §3.1
(p. 513) fixes Artin's convention for the Frobenius substitution. -/
public theorem_wanted exists_galoisRep_trace_det_frob_of_weight_one
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (hε : ε (-1) = -1)
    (f : ModularForm (Gamma1 N) 1) (hf : f ≠ 0)
    (hfε : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ τ : UpperHalfPlane,
      f (γ • τ) =
        ε ((γ 1 1 : ℤ) : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * f τ))
    (a : ℕ → ℂ)
    (ha : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      qCoeff f (p * n) + ε (p : ZMod N) * (if p ∣ n then qCoeff f (n / p) else 0) =
        a p * qCoeff f n) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ 𝔭 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)), 𝔭.IsMaximal →
          𝔭.under ℤ = Ideal.span {(p : ℤ)} →
          (∀ σ ∈ 𝔭.inertia (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ σ = 1) ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, IsArithFrobAt ℤ σ 𝔭 →
            (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = a p ∧
              (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N)) ∧
      ((∀ w : Fin 2 → ℂ, w ≠ 0 →
          ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : ℂ,
            (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).mulVec w ≠ c • w) ↔
        ∃ g : CuspForm (Gamma1 N) 1, ⇑g = ⇑f)

end ModularForm
