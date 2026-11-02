/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.Character

/-!
# Induced ray class characters (N428 Definition 22.12)

If `m1 ∣ m2`, a ray class character at `m2` is induced by one at `m1`
when their values agree on ideals coprime to `m2` under level change.
A character is primitive when it is induced only from the same modulus.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K] {m1 m2 : Modulus K}

/-- **Exponents of a modulus grow under divisibility.** Let $m_1$ and $m_2$ be moduli of a number
field $K$ with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the finite part
of $m_1$ and every real place of $m_1$ is a real place of $m_2$. Then for every finite prime $v$
of $K$ (a height-one prime of the ring of integers $\mathcal{O}_K$), the exponent of $v$ in the
finite part of $m_1$ is at most the exponent of $v$ in the finite part of $m_2$. -/
theorem finiteExponent_le_of_dvd (h : m1 ∣ m2)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteExponent m1 v ≤ finiteExponent m2 v := by
  have hfin := ((dvd_unfold m1 m2).mp h).1
  have hne : (m2.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using mem_nonZeroDivisors_iff_ne_zero.mp m2.finitePart.property
  unfold finiteExponent
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.mpr hne)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hfin)

private theorem coprime_le_of_dvd (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 ≤ coprimeFractionalIdeals m1 := by
  intro u hu v hv
  exact hu v (le_trans ((dvd_unfold m1 m2).mp h).1 hv)

/-- **Inclusion of coprime ideal groups under divisibility of moduli.** Let $m_1$ and $m_2$ be
moduli of a number field $K$ with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained
in the finite part of $m_1$ and every real place of $m_1$ is a real place of $m_2$. Then every
fractional ideal of $K$ coprime to $m_2$ is coprime to $m_1$, and this map is the inclusion
homomorphism from the group of fractional ideals coprime to $m_2$ into the group of fractional
ideals coprime to $m_1$. -/
def coprimeInclusion (h : m1 ∣ m2) :
    coprimeFractionalIdeals m2 →* coprimeFractionalIdeals m1 :=
  Subgroup.inclusion (coprime_le_of_dvd h)

/-- **Ray congruence to $1$ passes to divisors of the modulus.** Let $m_1$ and $m_2$ be moduli
of a number field $K$ with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the
finite part of $m_1$ and every real place of $m_1$ is a real place of $m_2$. If a nonzero element
$x$ of $K$ is congruent to $1$ modulo $m_2$ in the ray sense (its principal ideal is coprime to
$m_2$, for each prime $v$ dividing the finite part of $m_2$ either $x = 1$ or the exponent of
$v$ in $x - 1$ is at least its exponent in that finite part, and $x$ is positive at every real
place of $m_2$), then $x$ is congruent to $1$ modulo $m_1$ in the same sense. -/
theorem IsRayElementOne.of_dvd (h : m1 ∣ m2) {x : Kˣ}
    (hx : IsRayElementOne m2 x) : IsRayElementOne m1 x := by
  have hfin := ((dvd_unfold m1 m2).mp h).1
  have hinf := ((dvd_unfold m1 m2).mp h).2
  refine ⟨Subgroup.mem_comap.mpr (coprime_le_of_dvd h (Subgroup.mem_comap.mp hx.1)),
    ?_, ?_⟩
  · intro v hv
    rcases hx.2.1 v (le_trans hfin hv) with h1 | hle
    · exact Or.inl h1
    · exact Or.inr (le_trans (finiteExponent_le_of_dvd h v) hle)
  · intro w hw
    exact hx.2.2 w (Finset.mem_coe.mp (hinf (Finset.mem_coe.mpr hw)))

theorem rayGenerators_map_of_dvd (h : m1 ∣ m2) (y : coprimeFractionalIdeals m2)
    (hy : y ∈ rayGenerators m2) : coprimeInclusion h y ∈ rayGroup m1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 := IsRayElementOne.of_dvd h hx
  have heq : coprimeInclusion h ⟨toPrincipalIdeal (𝓞 K) K x, Subgroup.mem_comap.mp hx.1⟩ =
      ⟨toPrincipalIdeal (𝓞 K) K x, Subgroup.mem_comap.mp hx1.1⟩ := Subtype.ext rfl
  rw [heq]
  exact mem_rayGroup_of_isRayElementOne m1 x hx1

theorem rayGroup_le_comap_of_dvd (h : m1 ∣ m2) :
    rayGroup m2 ≤ (rayGroup m1).comap (coprimeInclusion h) := by
  apply rayGroup_closure_le
  intro y hy
  exact rayGenerators_map_of_dvd h y hy

/-- **Level-change map on ray class groups.** Let $m_1$ and $m_2$ be moduli of a number field $K$
with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the finite part of $m_1$
and every real place of $m_1$ is a real place of $m_2$. The inclusion of the group of fractional
ideals coprime to $m_2$ into the group of fractional ideals coprime to $m_1$ maps the ray group
modulo $m_2$ into the ray group modulo $m_1$, so it induces a group homomorphism from the ray
class group modulo $m_2$ to the ray class group modulo $m_1$, sending the class of an ideal
modulo $m_2$ to its class modulo $m_1$. -/
def RayClassGroup.mapOfDvd (h : m1 ∣ m2) : RayClassGroup m2 →* RayClassGroup m1 :=
  QuotientGroup.map (rayGroup m2) (rayGroup m1) (coprimeInclusion h) (rayGroup_le_comap_of_dvd h)

/-- **The level-change map on ray classes.** Let $m_1$ and $m_2$ be moduli of a number field $K$
with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the finite part of $m_1$
and every real place of $m_1$ is a real place of $m_2$. For every fractional ideal
$\mathfrak{a}$ of $K$ coprime to $m_2$, the level-change homomorphism from the ray class group
modulo $m_2$ to the ray class group modulo $m_1$ sends the ray class of $\mathfrak{a}$ modulo
$m_2$ to the ray class of $\mathfrak{a}$ modulo $m_1$ (an ideal coprime to $m_2$ is also coprime
to $m_1$). -/
@[simp] theorem RayClassGroup.mapOfDvd_rayClassMap (h : m1 ∣ m2)
    (x : coprimeFractionalIdeals m2) :
    mapOfDvd h (rayClassMap m2 x) = rayClassMap m1 (coprimeInclusion h x) := by
  simp only [mapOfDvd, rayClassMap, QuotientGroup.mk'_apply, QuotientGroup.map_mk]

/-- **Induced ray class character.** Let $m_1$ and $m_2$ be moduli of a number field $K$ with
$m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the finite part of $m_1$ and
every real place of $m_1$ is a real place of $m_2$. A ray class character $\chi_2$ modulo $m_2$
is induced by a ray class character $\chi_1$ modulo $m_1$ when $\chi_2 = \chi_1 \circ \pi$, where
$\pi$ is the level-change homomorphism from the ray class group modulo $m_2$ to the ray class
group modulo $m_1$ that sends the class of an ideal coprime to $m_2$ to its class modulo
$m_1$. -/
def RayClassCharacter.IsInducedBy (chi2 : RayClassCharacter m2)
    (chi1 : RayClassCharacter m1) (h : m1 ∣ m2) : Prop :=
  chi2 = chi1.comp (RayClassGroup.mapOfDvd h)

/-- **Induced characters agree on coprime ideals.** Let $m_1$ and $m_2$ be moduli of a number
field $K$ with $m_1 \mid m_2$, that is, the finite part of $m_2$ is contained in the finite part
of $m_1$ and every real place of $m_1$ is a real place of $m_2$. Let $\chi_1$ be a ray class
character modulo $m_1$ and $\chi_2$ a ray class character modulo $m_2$. Then $\chi_2$ is induced
by $\chi_1$ if and only if, for every fractional ideal $\mathfrak{a}$ of $K$ coprime to $m_2$,
the value of $\chi_2$ on the ray class of $\mathfrak{a}$ modulo $m_2$ equals the value of
$\chi_1$ on the ray class of $\mathfrak{a}$ modulo $m_1$ (an ideal coprime to $m_2$ is also
coprime to $m_1$). -/
theorem RayClassCharacter.isInducedBy_iff (chi2 : RayClassCharacter m2)
    (chi1 : RayClassCharacter m1) (h : m1 ∣ m2) :
    chi2.IsInducedBy chi1 h ↔ ∀ x : coprimeFractionalIdeals m2,
      pullback chi2 x = pullback chi1 (coprimeInclusion h x) := by
  constructor
  · intro hind x
    simp [show chi2 = chi1.comp (RayClassGroup.mapOfDvd h) from hind]
  · intro hall
    refine MonoidHom.ext fun q => ?_
    obtain ⟨x, rfl⟩ := rayClassMap_surjective m2 q
    rw [MonoidHom.comp_apply, RayClassGroup.mapOfDvd_rayClassMap,
      ← pullback_apply, ← pullback_apply]
    exact hall x

/-- **Primitive ray class character.** Let $m$ be a modulus of a number field $K$. A ray class
character $\chi$ modulo $m$ is primitive when, for every modulus $m_0$ of $K$ with $m_0 \mid m$
(the finite part of $m$ is contained in the finite part of $m_0$ and every real place of $m_0$
is a real place of $m$) and every ray class character $\chi_0$ modulo $m_0$ by which $\chi$ is
induced, $m_0 = m$. -/
def RayClassCharacter.IsPrimitive (chi : RayClassCharacter m2) : Prop :=
  ∀ (m0 : Modulus K) (chi0 : RayClassCharacter m0) (h : m0 ∣ m2),
    chi.IsInducedBy chi0 h → m0 = m2

/-- **Primitivity in terms of the level-change map.** Let $m$ be a modulus of a number field $K$.
A ray class character $\chi$ modulo $m$ is primitive if and only if, for every modulus $m_0$ of
$K$ with $m_0 \mid m$ (the finite part of $m$ is contained in the finite part of $m_0$ and every
real place of $m_0$ is a real place of $m$) and every ray class character $\chi_0$ modulo $m_0$
with $\chi = \chi_0 \circ \pi$, where $\pi$ is the level-change homomorphism from the ray class
group modulo $m$ to the ray class group modulo $m_0$, we have $m_0 = m$. -/
theorem RayClassCharacter.isPrimitive_iff (chi : RayClassCharacter m2) :
    chi.IsPrimitive ↔ ∀ (m0 : Modulus K) (chi0 : RayClassCharacter m0)
      (h : m0 ∣ m2), chi = chi0.comp (RayClassGroup.mapOfDvd h) → m0 = m2 :=
  Iff.rfl

end Modulus
end NumberField
