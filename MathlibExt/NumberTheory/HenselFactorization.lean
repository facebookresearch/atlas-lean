/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Monic Hensel factor lifting over adically complete rings

Clean-room implementation derived solely from the corrected mathematical
statement of the standard monic Hensel factor-lifting theorem together with
Mathlib's public APIs. No external formalization source was inspected
or copied.

Let `A` be a commutative ring that is `I`-adically complete for an ideal `I`,
and let `f : A[X]` be monic whose reduction modulo `I` factors as a product
of two monic coprime polynomials. Then the factorization lifts to `A`:
there exist monic `g h : A[X]` with `f = g * h` reducing to the given
residue factors. A corollary records the resulting degree equalities.
-/

@[expose] public section

namespace Polynomial

variable {A : Type*} [CommRing A]

/-- **Hensel lifting of monic coprime factorizations.** Let $A$ be a commutative ring and $I$ an
ideal of $A$ such that $A$ is $I$-adically complete, and let $f \in A[X]$ be monic. Suppose the
reduction of $f$ modulo $I$ equals $\bar g \bar h$, where $\bar g, \bar h \in (A/I)[X]$ are monic
and coprime (that is, $a \bar g + b \bar h = 1$ for some $a, b \in (A/I)[X]$). Then there exist
monic $g, h \in A[X]$ with $f = gh$ whose reductions modulo $I$ are $\bar g$ and $\bar h$
respectively.

The proof packages the residue factorization via the universal coprime factorization ring, lifts
its structure map through $I$-adic completeness, and evaluates the universal factors over $A$. -/
theorem exists_monic_coprime_factorization_of_isAdicComplete
    (I : Ideal A) [IsAdicComplete I A]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g_bar ∧
      h.map (Ideal.Quotient.mk I) = h_bar := by
  by_cases hnt : Nontrivial (A ⧸ I)
  · -- Nontrivial quotient: lift through the universal coprime ring.
    -- (`hnt` itself serves as the `Nontrivial` instance below.)
    have hdeg : f.natDegree = g_bar.natDegree + h_bar.natDegree := by
      have e1 : (f.map (Ideal.Quotient.mk I)).natDegree = f.natDegree :=
        hf.natDegree_map (Ideal.Quotient.mk I)
      have e2 : (g_bar * h_bar).natDegree =
          g_bar.natDegree + h_bar.natDegree :=
        hg.natDegree_mul hh
      rw [hfac] at e1
      rw [← e1]
      exact e2
    let pf : MonicDegreeEq A f.natDegree := MonicDegreeEq.mk f hf rfl
    let pg : MonicDegreeEq (A ⧸ I) g_bar.natDegree :=
      MonicDegreeEq.mk g_bar hg rfl
    let ph : MonicDegreeEq (A ⧸ I) h_bar.natDegree :=
      MonicDegreeEq.mk h_bar hh rfl
    have halg : algebraMap A (A ⧸ I) = Ideal.Quotient.mk I :=
      Ideal.Quotient.algebraMap_eq I
    have h1 : (pg : (A ⧸ I)[X]) * (ph : (A ⧸ I)[X]) =
        (pf : A[X]).map (algebraMap A (A ⧸ I)) := by
      have c1 : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have c2 : (ph : (A ⧸ I)[X]) = h_bar := rfl
      have c3 : (pf : A[X]) = f := rfl
      rw [c1, c2, c3, halg]
      exact hfac.symm
    have h2 : IsCoprime (pg : (A ⧸ I)[X]) (ph : (A ⧸ I)[X]) := by
      have c1 : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have c2 : (ph : (A ⧸ I)[X]) = h_bar := rfl
      rw [c1, c2]
      exact hcop
    obtain ⟨ψ, hψ⟩ :=
      Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := I)
        ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
          g_bar.natDegree h_bar.natDegree hdeg pf).symm ⟨(pg, ph), h1, h2⟩)
    set E := UniversalCoprimeFactorizationRing.homEquiv A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ with hE
    have hgh := E.2
    have nat1 := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ (Ideal.Quotient.mkₐ A I)
    have nat2 := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A
      g_bar.natDegree h_bar.natDegree hdeg pf ψ (Ideal.Quotient.mkₐ A I)
    rw [← hE] at nat1 nat2
    refine ⟨(E.1.1 : A[X]), (E.1.2 : A[X]), E.1.1.monic, E.1.2.monic, ?_,
      ?_, ?_⟩
    · have hprod : (E.1.1 : A[X]) * (E.1.2 : A[X]) =
          (pf : A[X]).map (algebraMap A A) := hgh.1
      have hmap : (pf : A[X]).map (algebraMap A A) = f := by
        have c : (pf : A[X]) = f := rfl
        rw [c, Algebra.algebraMap_self, Polynomial.map_id]
      rw [hprod]
      exact hmap.symm
    · have cg : (pg : (A ⧸ I)[X]) = g_bar := rfl
      have e1 : ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
            g_bar.natDegree h_bar.natDegree hdeg pf
            ((Ideal.Quotient.mkₐ A I).comp ψ)).1.1 : (A ⧸ I)[X]) = g_bar := by
        rw [hψ, Equiv.apply_symm_apply]
        exact cg
      have nat1c := congrArg
        (fun x : MonicDegreeEq (A ⧸ I) g_bar.natDegree => (x : (A ⧸ I)[X]))
        nat1
      simp only [MonicDegreeEq.map_coe, ← AlgHom.toRingHom_eq_coe,
        Ideal.Quotient.mkₐ_toRingHom] at nat1c
      have red1 : (E.1.1 : A[X]).map (Ideal.Quotient.mk I) = g_bar := by
        rw [e1] at nat1c
        exact nat1c.symm
      exact red1
    · have ch : (ph : (A ⧸ I)[X]) = h_bar := rfl
      have e2 : ((UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I)
            g_bar.natDegree h_bar.natDegree hdeg pf
            ((Ideal.Quotient.mkₐ A I).comp ψ)).1.2 : (A ⧸ I)[X]) = h_bar := by
        rw [hψ, Equiv.apply_symm_apply]
        exact ch
      have nat2c := congrArg
        (fun x : MonicDegreeEq (A ⧸ I) h_bar.natDegree => (x : (A ⧸ I)[X]))
        nat2
      simp only [MonicDegreeEq.map_coe, ← AlgHom.toRingHom_eq_coe,
        Ideal.Quotient.mkₐ_toRingHom] at nat2c
      have red2 : (E.1.2 : A[X]).map (Ideal.Quotient.mk I) = h_bar := by
        rw [e2] at nat2c
        exact nat2c.symm
      exact red2
  · -- Trivial quotient: every reduction equality holds vacuously.
    have : Subsingleton (A ⧸ I) := not_nontrivial_iff_subsingleton.mp hnt
    exact ⟨f, 1, hf, monic_one, by simp, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩

/-- **Hensel lifting of monic coprime factorizations, with degrees.** Let $A$ be a commutative
ring and $I$ an ideal of $A$ such that $A$ is $I$-adically complete and $A/I$ is not the zero
ring, and let $f \in A[X]$ be monic. Suppose the reduction of $f$ modulo $I$ equals
$\bar g \bar h$, where $\bar g, \bar h \in (A/I)[X]$ are monic and coprime (that is,
$a \bar g + b \bar h = 1$ for some $a, b \in (A/I)[X]$). Then there exist monic $g, h \in A[X]$
with $f = gh$ whose reductions modulo $I$ are $\bar g$ and $\bar h$ respectively, and such that
$\deg g = \deg \bar g$ and $\deg h = \deg \bar h$. -/
theorem exists_monic_coprime_factorization_of_isAdicComplete_natDegree
    (I : Ideal A) [IsAdicComplete I A] [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic)
    (g_bar h_bar : (A ⧸ I)[X])
    (hg : g_bar.Monic) (hh : h_bar.Monic)
    (hfac : f.map (Ideal.Quotient.mk I) = g_bar * h_bar)
    (hcop : IsCoprime g_bar h_bar) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g_bar ∧
      h.map (Ideal.Quotient.mk I) = h_bar ∧
      g.natDegree = g_bar.natDegree ∧ h.natDegree = h_bar.natDegree := by
  obtain ⟨g, h, hgM, hhM, hgh, hr1, hr2⟩ :=
    exists_monic_coprime_factorization_of_isAdicComplete I f hf g_bar h_bar
      hg hh hfac hcop
  have e1 : (g.map (Ideal.Quotient.mk I)).natDegree = g.natDegree :=
    hgM.natDegree_map (Ideal.Quotient.mk I)
  have e2 : (h.map (Ideal.Quotient.mk I)).natDegree = h.natDegree :=
    hhM.natDegree_map (Ideal.Quotient.mk I)
  rw [hr1] at e1
  rw [hr2] at e2
  exact ⟨g, h, hgM, hhM, hgh, hr1, hr2, e1.symm, e2.symm⟩

end Polynomial
