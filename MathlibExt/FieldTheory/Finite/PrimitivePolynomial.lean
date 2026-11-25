/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive polynomials over finite fields

Reusable finite-field version of ATLAS Definition 3.14.
Distinct from `Polynomial.IsPrimitive`, which means primitive content.
-/

@[expose] public section

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- **Primitive polynomial over a finite field.** Let $F$ be a finite field with $q$ elements,
let $f \in F[X]$, and let $n$ be the degree of $f$ (with $n = 0$ if $f = 0$). Then $f$ is
primitive if it is monic, it is irreducible, and the class of $X$ in the quotient ring
$F[X]/(f)$ has multiplicative order $q^n - 1$. -/
def IsPrimitivePolynomial [Finite F] (f : F[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1

variable [Finite F]

/-- **Primitive polynomials are monic.** Every primitive polynomial over a finite field is
monic. -/
theorem IsPrimitivePolynomial.monic {f : F[X]}
    (hf : f.IsPrimitivePolynomial) : f.Monic :=
  hf.1

/-- **Primitive polynomials are irreducible.** Every primitive polynomial over a finite field is
irreducible. -/
theorem IsPrimitivePolynomial.irreducible {f : F[X]}
    (hf : f.IsPrimitivePolynomial) : Irreducible f :=
  hf.2.1

/-- **Order of the root of a primitive polynomial.** Let $F$ be a finite field with $q$ elements
and let $f \in F[X]$ be a primitive polynomial of degree $n$. Then the class of $X$ in the
quotient ring $F[X]/(f)$ has multiplicative order $q^n - 1$. -/
theorem IsPrimitivePolynomial.root_orderOf {f : F[X]}
    (hf : f.IsPrimitivePolynomial) :
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  hf.2.2

/-- **Defining characterization of primitive polynomials.** Let $F$ be a finite field with $q$
elements, let $f \in F[X]$, and let $n$ be the degree of $f$ (with $n = 0$ if $f = 0$). Then $f$
is primitive if and only if $f$ is monic, $f$ is irreducible, and the class of $X$ in the
quotient ring $F[X]/(f)$ has multiplicative order $q^n - 1$. -/
theorem IsPrimitivePolynomial.iff {f : F[X]} :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  Iff.rfl

/-- **Primitive polynomials via primitive roots of unity.** Let $F$ be a finite field with $q$
elements, let $f \in F[X]$, and let $n$ be the degree of $f$ (with $n = 0$ if $f = 0$). Let
$\alpha$ be the class of $X$ in the quotient ring $F[X]/(f)$. Then $f$ is primitive if and only
if $f$ is monic, $f$ is irreducible, and $\alpha$ is a primitive $(q^n - 1)$-th root of unity,
that is, $\alpha^{q^n - 1} = 1$ and $q^n - 1$ divides every natural number $l$ with
$\alpha^l = 1$. -/
theorem IsPrimitivePolynomial.iff_isPrimitiveRoot {f : F[X]} :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      IsPrimitiveRoot (AdjoinRoot.root f)
        (Nat.card F ^ f.natDegree - 1) := by
  unfold IsPrimitivePolynomial
  exact and_congr Iff.rfl
    (and_congr Iff.rfl (IsPrimitiveRoot.iff_orderOf).symm)

variable (p : ℕ) [Fact p.Prime]

/-- **Primitive polynomials over $\mathbb{Z}/p\mathbb{Z}$.** Let $p$ be a prime, let $f$ be a
polynomial over $\mathbb{Z}/p\mathbb{Z}$, and let $n$ be the degree of $f$ (with $n = 0$ if
$f = 0$). Then $f$ is primitive if and only if $f$ is monic, $f$ is irreducible, and the class of
$X$ in the quotient ring $(\mathbb{Z}/p\mathbb{Z})[X]/(f)$ has multiplicative order $p^n - 1$.

Source: ATLAS Definition 3.14. -/
theorem IsPrimitivePolynomial.zmod_iff (f : (ZMod p)[X]) :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
  unfold IsPrimitivePolynomial
  rw [Nat.card_eq_fintype_card, ZMod.card p]

end Polynomial
