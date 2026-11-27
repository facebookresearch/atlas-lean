/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_Field_exists_finrank_eq_pow_and_fieldRange_eq_
iterateFrobenius_of_isPurelyInseparable.lean`
and
`P2M/Sol/S_Field_exists_finrank_eq_pow_and_fieldRange_eq_
iterateFrobenius_of_isPurelyInseparable.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
The adaptations: the helpers are private, the proof text is rewrapped to 100 columns
and adjusted for Mathlib style (`have` for `haveI`, named hypotheses), and the theorem
has a docstring.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.Relrank

@[expose] public section

namespace Field

variable {E : Type*} [Field E] (p : ℕ) [Fact p.Prime] [CharP E p]

private noncomputable def frobeniusSubfield (n : ℕ) : Subfield E :=
  Subfield.map (iterateFrobenius E p n) ⊤

private lemma frobeniusSubfield_zero :
    frobeniusSubfield p 0 = (⊤ : Subfield E) := by
  ext x
  simp only [frobeniusSubfield, iterateFrobenius_zero, Subfield.mem_map,
    RingHom.id_apply, Subfield.mem_top, true_and, exists_eq]

private lemma frobeniusSubfield_succ (n : ℕ) :
    frobeniusSubfield p (n + 1) =
      Subfield.map (frobenius E p) (frobeniusSubfield p n) := by
  rw [frobeniusSubfield, frobeniusSubfield, Subfield.map_map,
    ← iterateFrobenius_one, ← iterateFrobenius_add, Nat.add_comm]

private lemma frobeniusSubfield_one :
    frobeniusSubfield p 1 = (frobenius E p).fieldRange := by
  rw [frobeniusSubfield, iterateFrobenius_one, RingHom.fieldRange_eq_map]

private lemma map_frobenius_le (S : Subfield E) :
    Subfield.map (frobenius E p) S ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  rw [frobenius_def]
  exact pow_mem hx p

private lemma frobeniusSubfield_exponent_le (S : Subfield E)
    [IsPurelyInseparable S E] [FiniteDimensional S E] :
    frobeniusSubfield p (IsPurelyInseparable.exponent S E) ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  rw [iterateFrobenius_def]
  obtain ⟨y, hy⟩ :=
    RingHom.mem_range.1 (IsPurelyInseparable.exponent_def' S p x)
  rw [← hy]
  exact y.2

private lemma le_frobeniusSubfield_one
    (hp : Module.finrank (frobenius E p).fieldRange E = p)
    (S : Subfield E) [IsPurelyInseparable S E] [FiniteDimensional S E]
    (hS : S ≠ ⊤) :
    S ≤ frobeniusSubfield p 1 := by
  have hprime : p.Prime := Fact.out
  have hE1top :
      (frobeniusSubfield (E := E) p 1).relfinrank ⊤ = p := by
    rw [Subfield.relfinrank_top_right, frobeniusSubfield_one]; exact hp
  have hmul := Subfield.relfinrank_mul_relfinrank
    (le_sup_left : frobeniusSubfield p 1 ≤ frobeniusSubfield p 1 ⊔ S)
    (le_top : frobeniusSubfield p 1 ⊔ S ≤ ⊤)
  rw [hE1top] at hmul
  have hdvd : (frobeniusSubfield p 1 ⊔ S).relfinrank ⊤ ∣ p :=
    Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime hprime).1 hdvd with h1 | h2
  · exfalso
    have htop : (⊤ : Subfield E) ≤ frobeniusSubfield p 1 ⊔ S :=
      Subfield.relfinrank_eq_one_iff.1 h1
    have key : ∀ n : ℕ, (⊤ : Subfield E) ≤
        frobeniusSubfield p n ⊔ S := by
      intro n
      induction n with
      | zero => rw [frobeniusSubfield_zero]; exact le_sup_left
      | succ n ih =>
        have hmono : Subfield.map (frobenius E p) ⊤ ≤
            Subfield.map (frobenius E p)
              (frobeniusSubfield p n ⊔ S) :=
          (Subfield.gc_map_comap (frobenius E p)).monotone_l ih
        rw [Subfield.map_sup, ← frobeniusSubfield_succ] at hmono
        have hE1 : frobeniusSubfield p 1 ≤
            frobeniusSubfield p (n + 1) ⊔ S := by
          rw [frobeniusSubfield_one, RingHom.fieldRange_eq_map]
          exact hmono.trans (sup_le_sup_left (map_frobenius_le p S) _)
        exact htop.trans (sup_le hE1 le_sup_right)
    have hle : (⊤ : Subfield E) ≤ S :=
      (key (IsPurelyInseparable.exponent S E)).trans
        (sup_le (frobeniusSubfield_exponent_le p S) le_rfl)
    exact hS (top_le_iff.1 hle)
  · rw [h2] at hmul
    have h1 : (frobeniusSubfield p 1).relfinrank
        (frobeniusSubfield p 1 ⊔ S) = 1 := by
      have hmul' : (frobeniusSubfield p 1).relfinrank
          (frobeniusSubfield p 1 ⊔ S) * p = 1 * p := by
        rw [hmul, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hprime.pos hmul'
    exact le_sup_right.trans (Subfield.relfinrank_eq_one_iff.1 h1)

private theorem frobeniusSubfield_core
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∀ (d : ℕ) (S : Subfield E), IsPurelyInseparable S E →
      FiniteDimensional S E → Module.finrank S E = d →
      ∃ r : ℕ, d = p ^ r ∧ S = frobeniusSubfield p r := by
  have hprime : p.Prime := Fact.out
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hPI hFD hd
  by_cases hS : S = ⊤
  · subst hS
    refine ⟨0, ?_, (frobeniusSubfield_zero p).symm⟩
    rw [← hd, pow_zero, ← Subfield.relfinrank_top_right,
      Subfield.relfinrank_self]
  · have hle : S ≤ frobeniusSubfield p 1 :=
      le_frobeniusSubfield_one p hp S hS
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subfield E,
        S₁ = Subfield.comap (frobenius E p) S := ⟨_, rfl⟩
    have hmap : Subfield.map (frobenius E p) S₁ = S := by
      rw [hS₁]
      apply Subfield.map_comap_eq_self
      rw [← frobeniusSubfield_one]; exact hle
    have hrel : Module.finrank S E = Module.finrank S₁ E * p := by
      rw [← Subfield.relfinrank_top_right,
        ← Subfield.relfinrank_top_right,
        ← Subfield.relfinrank_mul_relfinrank hle le_top]
      congr 1
      · rw [frobeniusSubfield, iterateFrobenius_one, ← hmap,
          Subfield.relfinrank_map_map]
      · rw [Subfield.relfinrank_top_right, frobeniusSubfield_one]
        exact hp
    have hpos : 0 < Module.finrank S E := Module.finrank_pos
    have hpos₁ : 0 < Module.finrank S₁ E := by
      rcases Nat.eq_zero_or_pos (Module.finrank S₁ E) with h | h
      · rw [h, zero_mul] at hrel; omega
      · exact h
    have : FiniteDimensional S₁ E := Module.finite_of_finrank_pos hpos₁
    have : IsPurelyInseparable S₁ E := by
      rw [isPurelyInseparable_iff_pow_mem S₁ p]
      intro x
      obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem S p x
      obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
      have hmem : x ^ p ^ (n + 1) ∈ S₁ := by
        rw [hS₁, Subfield.mem_comap, frobenius_def, pow_succ, pow_mul,
          ← hy]
        exact pow_mem (pow_mem y.2 _) _
      exact ⟨n + 1, RingHom.mem_range.2 ⟨⟨_, hmem⟩, rfl⟩⟩
    have hlt : Module.finrank S₁ E < d := by
      rw [← hd, hrel]
      have hlt' := (Nat.mul_lt_mul_left hpos₁).2 hprime.one_lt
      rwa [mul_one] at hlt'
    obtain ⟨r, hr, hS₁r⟩ := ih _ hlt S₁ ‹_› ‹_› rfl
    refine ⟨r + 1, ?_, ?_⟩
    · rw [← hd, hrel, hr, pow_succ]
    · rw [← hmap, hS₁r, frobeniusSubfield_succ]

/-- **Purely inseparable extensions and iterated Frobenius images.** Let $p$ be a prime and let
$E/M$ be a finite purely inseparable extension of fields of characteristic $p$ such that $E$ has
degree $p$ over its Frobenius image $E^p$, the subfield of $p$-th powers: $[E : E^p] = p$. Then
there is a natural number $r$ with $[E : M] = p^r$, and the image of $M$ in $E$ equals $E^{p^r}$,
the subfield of $p^r$-th powers, which is the image of the $r$-th iterated Frobenius endomorphism
of $E$. -/
public theorem
    exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    {M : Type*} [Field M] [Algebra M E] [FiniteDimensional M E]
    [IsPurelyInseparable M E]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange =
        (iterateFrobenius E p r).fieldRange := by
  have : CharP M p := (Algebra.charP_iff M E p).2 inferInstance
  have hfr : Module.finrank M E =
      Module.finrank (algebraMap M E).fieldRange E := by
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingHom.rangeRestrictFieldEquiv (algebraMap M E))
      (RingEquiv.refl E) ?_
    ext x; rfl
  have : FiniteDimensional (algebraMap M E).fieldRange E :=
    Module.finite_of_finrank_pos (hfr ▸ Module.finrank_pos)
  have : IsPurelyInseparable (algebraMap M E).fieldRange E := by
    rw [isPurelyInseparable_iff_pow_mem (algebraMap M E).fieldRange p]
    intro x
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem M p x
    obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
    exact ⟨n, RingHom.mem_range.2
      ⟨⟨x ^ p ^ n, RingHom.mem_fieldRange.2 ⟨y, hy⟩⟩, rfl⟩⟩
  obtain ⟨r, hr, hR⟩ := frobeniusSubfield_core p hp _
    (algebraMap M E).fieldRange ‹_› ‹_› rfl
  exact ⟨r, hfr.trans hr, hR.trans (by
    rw [frobeniusSubfield, RingHom.fieldRange_eq_map])⟩

end Field
