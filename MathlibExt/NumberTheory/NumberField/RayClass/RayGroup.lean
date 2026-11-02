/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.Modulus
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Ray groups attached to a modulus (N403 foundation)

Built over `NumberField.Modulus`, whose infinite-place multiplication
uses union, representing truncated exponent addition `min (m v + n v) 1`
(the ATLAS-extracted `max` formula was a typo).
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Primes dividing a modulus.** Let $\mathfrak m$ be a modulus of a number field $K$, with finite
part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$. A nonzero prime ideal $\mathfrak p$ of
$\mathcal O_K$ lies in the finite support of $\mathfrak m$ when
$\mathfrak m_0 \subseteq \mathfrak p$, that is, when $\mathfrak p$ divides $\mathfrak m_0$. -/
def finiteSupported (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal

/-- **Exponent of a modulus at a prime.** Let $\mathfrak m$ be a modulus of a number field $K$, with
finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$. For a nonzero prime ideal
$\mathfrak p$ of $\mathcal O_K$, the finite exponent of $\mathfrak m$ at $\mathfrak p$ is the
integer $v_{\mathfrak p}(\mathfrak m_0)$, the exponent of $\mathfrak p$ in the prime factorization
of $\mathfrak m_0$. -/
def finiteExponent (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v
    ((m.finitePart : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

/-- **Fractional ideals coprime to a modulus.** Let $\mathfrak m$ be a modulus of a number field
$K$, with finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$. For an invertible
fractional ideal $I$ of $\mathcal O_K$ and a nonzero prime ideal $\mathfrak p$, write
$v_{\mathfrak p}(I)$ for the exponent of $\mathfrak p$ in the factorization of $I$. The fractional
ideals coprime to $\mathfrak m$ form the subgroup of the group of invertible fractional ideals of
$\mathcal O_K$ consisting of those $I$ with $v_{\mathfrak p}(I) = 0$ for every nonzero prime ideal
$\mathfrak p$ of $\mathcal O_K$ containing $\mathfrak m_0$. -/
def coprimeFractionalIdeals (m : Modulus K) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier :=
    { u |
      ∀ v, finiteSupported m v →
        FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K) = 0 }
  one_mem' := by
    intro v _
    rw [Units.val_one]
    exact FractionalIdeal.count_one K v
  mul_mem' := by
    intro a b ha hb v hv
    rw [Units.val_mul]
    rw [FractionalIdeal.count_mul K v (Units.ne_zero a) (Units.ne_zero b)]
    rw [ha v hv, hb v hv, add_zero]
  inv_mem' := by
    intro a ha v hv
    rw [Units.val_inv_eq_inv_val]
    rw [FractionalIdeal.count_inv K v (a : FractionalIdeal (𝓞 K)⁰ K), ha v hv, neg_zero]

theorem mem_coprimeFractionalIdeals_iff (m : Modulus K)
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    u ∈ coprimeFractionalIdeals m ↔
      ∀ v, finiteSupported m v →
        FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
  Iff.rfl

/-- **Elements coprime to a modulus.** Let $\mathfrak m$ be a modulus of a number field $K$, with
finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$. The elements coprime to
$\mathfrak m$ form the subgroup of $K^\times$ consisting of those $x$ whose principal fractional
ideal $(x)$ is coprime to $\mathfrak m$, that is, has exponent $0$ at every nonzero prime ideal
$\mathfrak p$ of $\mathcal O_K$ containing $\mathfrak m_0$. -/
def rayElements (m : Modulus K) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal (𝓞 K) K)
    (coprimeFractionalIdeals m)

theorem mem_rayElements_iff (m : Modulus K) (x : Kˣ) :
    x ∈ rayElements m ↔
      toPrincipalIdeal (𝓞 K) K x ∈
        coprimeFractionalIdeals m :=
  Subgroup.mem_comap

/-- **Multiplicative congruence to one at the finite part.** Let $\mathfrak m$ be a modulus of a
number field $K$, with finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$. For a
nonzero prime ideal $\mathfrak p$ of $\mathcal O_K$, write $v_{\mathfrak p}(I)$ for the exponent of
$\mathfrak p$ in the factorization of a nonzero fractional ideal $I$ of $\mathcal O_K$, and for
$y \in K$ write $v_{\mathfrak p}(y) = v_{\mathfrak p}((y))$ (with $v_{\mathfrak p}(0) = 0$). An
element $x \in K^\times$ is congruent to $1$ at the finite part of $\mathfrak m$ when, for every
nonzero prime ideal $\mathfrak p$ of $\mathcal O_K$ containing $\mathfrak m_0$, either $x = 1$ or
$v_{\mathfrak p}(\mathfrak m_0) \le v_{\mathfrak p}(x - 1)$. -/
def CongruentOneAtFinitePart (m : Modulus K) (x : Kˣ) : Prop :=
  ∀ v, finiteSupported m v →
    (x : K) = 1 ∨
      finiteExponent m v ≤
        FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) - 1))

/-- **Positivity at the infinite part of a modulus.** Let $\mathfrak m$ be a modulus of a number
field $K$, with infinite part the finite set $\mathfrak m_\infty$ of real places of $K$. An element
$x \in K^\times$ is positive at the infinite part of $\mathfrak m$ when $\sigma_w(x) > 0$ for every
real place $w \in \mathfrak m_\infty$, where $\sigma_w \colon K \to \mathbb R$ is the real
embedding corresponding to $w$. -/
def PositiveAtInfinitePart (m : Modulus K) (x : Kˣ) : Prop :=
  ∀ w : RealPlace K, w ∈ m.infinitePart →
    InfinitePlace.embedding_of_isReal w.property (x : K) > 0

/-- **Elements congruent to one modulo a modulus.** Let $\mathfrak m$ be a modulus of a number field
$K$, with finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$ and infinite part the
finite set $\mathfrak m_\infty$ of real places of $K$. For a nonzero prime ideal $\mathfrak p$ of
$\mathcal O_K$, write $v_{\mathfrak p}(I)$ for the exponent of $\mathfrak p$ in the factorization
of a nonzero fractional ideal $I$ of $\mathcal O_K$, and for $y \in K$ write
$v_{\mathfrak p}(y) = v_{\mathfrak p}((y))$ (with $v_{\mathfrak p}(0) = 0$); for a real place $w$
write $\sigma_w \colon K \to \mathbb R$ for the corresponding real embedding. An element
$x \in K^\times$ is congruent to $1$ modulo $\mathfrak m$ when, for every nonzero prime ideal
$\mathfrak p$ of $\mathcal O_K$ containing $\mathfrak m_0$, $v_{\mathfrak p}(x) = 0$ and either
$x = 1$ or $v_{\mathfrak p}(\mathfrak m_0) \le v_{\mathfrak p}(x - 1)$, and $\sigma_w(x) > 0$ for
every real place $w \in \mathfrak m_\infty$. -/
def IsRayElementOne (m : Modulus K) (x : Kˣ) : Prop :=
  x ∈ rayElements m ∧ CongruentOneAtFinitePart m x ∧ PositiveAtInfinitePart m x

theorem IsRayElementOne.mem_rayElements {m : Modulus K} {x : Kˣ}
    (h : IsRayElementOne m x) : x ∈ rayElements m :=
  h.1

theorem IsRayElementOne.congruent {m : Modulus K} {x : Kˣ}
    (h : IsRayElementOne m x) : CongruentOneAtFinitePart m x :=
  h.2.1

theorem IsRayElementOne.positive {m : Modulus K} {x : Kˣ}
    (h : IsRayElementOne m x) : PositiveAtInfinitePart m x :=
  h.2.2

/-- **Generators of the ray group.** Let $\mathfrak m$ be a modulus of a number field $K$. The ray
generators of $\mathfrak m$ are the fractional ideals coprime to $\mathfrak m$ of the form $(x)$,
the principal fractional ideal of an element $x \in K^\times$ that is congruent to $1$ modulo
$\mathfrak m$. -/
def rayGenerators (m : Modulus K) : Set (coprimeFractionalIdeals m) :=
  { y |
    ∃ x : Kˣ, ∃ hx : IsRayElementOne m x,
      (⟨toPrincipalIdeal (𝓞 K) K x,
        Subgroup.mem_comap.mp hx.1⟩ :
        coprimeFractionalIdeals m) = y }

/-- **The ray group of a modulus.** Let $\mathfrak m$ be a modulus of a number field $K$. The ray
group of $\mathfrak m$ is the subgroup of the group of fractional ideals coprime to $\mathfrak m$
generated by the principal ideals $(x)$ of the elements $x \in K^\times$ congruent to $1$ modulo
$\mathfrak m$. -/
def rayGroup (m : Modulus K) : Subgroup (coprimeFractionalIdeals m) :=
  Subgroup.closure (rayGenerators m)

theorem rayGenerators_mem_of_isRayElementOne (m : Modulus K) (x : Kˣ)
    (hx : IsRayElementOne m x) :
    (⟨toPrincipalIdeal (𝓞 K) K x,
      Subgroup.mem_comap.mp hx.1⟩ :
      coprimeFractionalIdeals m) ∈ rayGenerators m :=
  ⟨x, hx, rfl⟩

theorem mem_rayGroup_of_isRayElementOne (m : Modulus K) (x : Kˣ)
    (hx : IsRayElementOne m x) :
    (⟨toPrincipalIdeal (𝓞 K) K x,
      Subgroup.mem_comap.mp hx.1⟩ :
      coprimeFractionalIdeals m) ∈ rayGroup m :=
  Subgroup.subset_closure (rayGenerators_mem_of_isRayElementOne m x hx)

theorem rayGroup_closure_le {m : Modulus K}
    {H : Subgroup (coprimeFractionalIdeals m)}
    (h : rayGenerators m ⊆ (↑H : Set _)) : rayGroup m ≤ H :=
  (Subgroup.closure_le H).2 h

theorem congruentOneAtFinitePart_one (m : Modulus K) :
    CongruentOneAtFinitePart m 1 := fun _ _ => Or.inl rfl

theorem positiveAtInfinitePart_one (m : Modulus K) :
    PositiveAtInfinitePart m 1 := by
  intro w _
  rw [Units.val_one, map_one]
  exact one_pos

theorem isRayElementOne_one (m : Modulus K) : IsRayElementOne m 1 :=
  ⟨one_mem _, congruentOneAtFinitePart_one m, positiveAtInfinitePart_one m⟩

end Modulus
end NumberField
