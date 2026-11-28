/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality
import MathlibExt.GroupTheory.IrreducibleCharacterBasis

/-!
# Blocks of defect zero and commutator counts in simple groups

For the alternating group on five letters at the prime two, there is one defect-zero character
and there are three conjugacy classes whose elements have an odd commutator count. This refutes
the equality both for simple groups and for arbitrary finite groups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov). UnsolvedMath record UM-00700898 (`KOU-12.80`), dataset
ulamai/UnsolvedMath v1.8.0.

Blocks of defect zero are counted by the irreducible complex characters of `p`-defect zero: each
such block contains exactly one irreducible character `χ`, characterized by `|G|ₚ ∣ χ(1)` (Brauer);
characters are compared as functions. Both parts are stated for primes `p` dividing `|G|`: for `p ∤
|G|` the literal claim fails trivially (for `G = ℤ₂`, `p = 3` there are two blocks of defect zero
and one such class), and both counterexamples of the Archive have `p ∣ |G|`. Simple is
`IsSimpleGroup`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted

open scoped commutatorElement

/-- **Characters of $p$-defect zero.** For a natural number $p$ and a group $G$, the set of
characters $\chi \colon G \to \mathbb{C}$ of irreducible finite-dimensional complex representations
of $G$ whose degree is divisible by $p^a$, where $a$ is the exponent of $p$ in the prime
factorization of the order $|G|$ (and $a = 0$ when $G$ is infinite or $p$ is not prime).

For a prime $p$ and a finite group $G$, each $p$-block of defect zero contains exactly one
irreducible character, and every such character forms a block of defect zero (Brauer), so these
characters count the $p$-blocks of defect zero. -/
def defectZeroCharacters (p : ℕ) (G : Type) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ ∧
      p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V}

/-- **Number of solutions of a commutator equation.** For an element $g$ of a group $G$, the
number of pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$, taken to be $0$ when
there are infinitely many such pairs. -/
noncomputable def commutatorSolutionCount {G : Type*} [Group G] (g : G) : ℕ :=
  Nat.card {xy : G × G // ⁅xy.1, xy.2⁆ = g}

/-- **Conjugacy classes with commutator count not divisible by $p$.** For a natural number $p$ and
a group $G$, the set of conjugacy classes of $G$ containing an element $g$ such that the number of
pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$ (taken to be $0$ when there are
infinitely many) is not divisible by $p$. -/
def nondivisibleCommutatorClasses (p : ℕ) (G : Type*) [Group G] : Set (ConjClasses G) :=
  {c | ∃ g : G, ConjClasses.mk g = c ∧ ¬ p ∣ commutatorSolutionCount g}

/-- **Kourovka Problem 12.80(a): blocks of defect zero and commutator equations.** For every prime
$p$ and every finite group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$.

Each $p$-block of defect zero contains exactly one irreducible character, and every irreducible
character of $p$-defect zero forms such a block (Brauer), so this is K. W. Roggenkamp's question
whether the number of $p$-blocks of defect zero equals that number of classes. -/
def defectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

/-- **Kourovka Problem 12.80(b): the case of simple groups.** For every prime $p$ and every
finite simple group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$. -/
def simpleDefectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

open Equiv Equiv.Perm BurnsidePaqb CategoryTheory
open MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted

private abbrev A₅ : Type := alternatingGroup (Fin 5)

private def threeCycle : A₅ := ⟨swap 0 1 * swap 1 2, by simp [mem_alternatingGroup]⟩

private def fiveCycle : A₅ := ⟨finRotate 5, finRotate_bit1_mem_alternatingGroup (n := 2)⟩

private def twoSwaps : A₅ := ⟨swap 0 1 * swap 2 3, by simp [mem_alternatingGroup]⟩

-- Identity, double transposition, 3-cycle, and representatives of the two 5-cycle classes.
private def representative : Fin 5 → A₅ := ![1, twoSwaps, threeCycle, fiveCycle, fiveCycle ^ 2]

private local instance decidableConjugacy : DecidableRel (IsConj : A₅ → A₅ → Prop) := fun g h =>
  decidable_of_iff (∃ k : A₅, k * g * k⁻¹ = h) isConj_iff.symm

private theorem card_conjClasses : Fintype.card (ConjClasses A₅) = 5 := by
  decide +kernel

private noncomputable def classEquiv : Fin 5 ≃ ConjClasses A₅ := by
  let f (i : Fin 5) := ConjClasses.mk (representative i)
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨?_, by rw [Fintype.card_fin, card_conjClasses]⟩
  have hinj : ∀ i j : Fin 5, IsConj (representative i) (representative j) → i = j := by
    decide +kernel
  exact fun _ _ e => hinj _ _ (ConjClasses.mk_eq_mk_iff_isConj.mp e)

private theorem commutatorSolutionCount_eq_of_isConj {G : Type*} [Group G] {g h : G}
    (hc : IsConj g h) : commutatorSolutionCount g = commutatorSolutionCount h := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hc
  let e := MulAut.conj k
  apply Nat.card_congr
  apply (e.toEquiv.prodCongr e.toEquiv).subtypeEquiv
  intro xy
  change ⁅xy.1, xy.2⁆ = g ↔ ⁅e xy.1, e xy.2⁆ = e g
  rw [← map_commutatorElement, e.injective.eq_iff]

private def solutionCard (i : Fin 5) : ℕ :=
  Fintype.card {xy : A₅ × A₅ // ⁅xy.1, xy.2⁆ = representative i}

private theorem card_odd_representatives :
    Fintype.card {i : Fin 5 // ¬ 2 ∣ solutionCard i} = 3 := by
  have counts : solutionCard = ![300, 32, 63, 65, 65] := funext (by decide +kernel)
  rw [counts]
  decide

private theorem class_count : Nat.card (nondivisibleCommutatorClasses 2 A₅) = 3 := by
  rw [← card_odd_representatives, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.symm
  apply classEquiv.subtypeEquiv
  intro i
  change (¬ 2 ∣ solutionCard i) ↔ ∃ g : A₅, ConjClasses.mk g = ConjClasses.mk (representative i) ∧ _
  have he : solutionCard i = commutatorSolutionCount (representative i) :=
    Nat.card_eq_fintype_card.symm
  rw [he]
  constructor
  · exact fun h => ⟨_, rfl, h⟩
  · rintro ⟨g, eg, hg⟩
    rwa [← commutatorSolutionCount_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp eg)]

private theorem card_group : Nat.card A₅ = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_irreps : Fintype.card (Irr A₅) = 5 := by
  let f (i : Irr A₅) : {χ : A₅ → ℂ // ∃ V : FDRep ℂ A₅, Simple V ∧ V.character = χ} :=
    ⟨Irr.charFun A₅ i, (Irr.repBundle A₅ i).1, (Irr.repBundle A₅ i).2, Irr.charFun_repBundle A₅ i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun _ _ e => Irr.charFun_inj A₅ (congrArg Subtype.val e), ?_⟩
    rintro ⟨_, V, hV, rfl⟩
    exact ⟨Quotient.mk _ ⟨V, hV⟩, rfl⟩
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.ofBijective f hf),
    card_irrCharacters_eq_card_conjClasses, Nat.card_eq_fintype_card, card_conjClasses]

private theorem square_residue (n : ℕ) :
    n ^ 2 % 8 + 3 * (if Odd n then 1 else 0) + 4 * (if 4 ∣ n then 1 else 0) = 4 := by
  have tab : ∀ r : Fin 8, r.val ^ 2 % 8 + 3 * (if r.val % 2 = 1 then 1 else 0) +
      4 * (if r.val % 4 = 0 then 1 else 0) = 4 := by decide
  simpa only [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8), Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8),
    ← Nat.pow_mod, Nat.odd_iff, Nat.dvd_iff_mod_eq_zero] using
    tab ⟨n % 8, Nat.mod_lt _ (by decide)⟩

private theorem two_part_card : 2 ^ (Nat.card A₅).factorization 2 = 4 := by
  rw [card_group, Nat.factorization_eq_card_pow_dvd_of_lt Nat.prime_two (by decide)
    (show 60 < 2 ^ 6 by decide)]
  decide

private theorem character_count : Nat.card (defectZeroCharacters 2 A₅) = 1 := by
  classical
  let d (i : Irr A₅) := Module.finrank ℂ (Irr.repBundle A₅ i).1
  have hcast (i : Irr A₅) : Irr.charFun A₅ i 1 = (d i : ℂ) := Irr.charFun_one A₅ i
  have hsum := sum_deg_sq A₅
  simp only [hcast, ← Nat.cast_pow, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [← Nat.card_eq_fintype_card, card_group] at hsum
  let s := Finset.univ.filter fun i => 4 ∣ d i
  -- Odd squares contribute 1 modulo 8, while even squares contribute either 0 or 4.
  -- The trivial character has odd degree. Among five squares summing to 60 these
  -- residues force four odd degrees and exactly one degree divisible by four.
  have hs : s.card = 1 := by
    have hres := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun (i : Irr A₅) _ => square_residue (d i))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id,
      Finset.sum_const, Finset.card_univ, card_irreps, smul_eq_mul] at hres
    have hmod := congrArg (· % 8) hsum
    rw [Finset.sum_nat_mod] at hmod
    have hpos : 0 < (Finset.univ.filter fun i => Odd (d i)).card := by
      apply Finset.card_pos.mpr
      refine ⟨Irr.triv A₅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      have ht : d (Irr.triv A₅) = 1 := by
        exact_mod_cast (hcast (Irr.triv A₅)).symm.trans (Irr.charFun_triv A₅ 1)
      simp [ht]
    dsimp only [s]
    omega
  -- Identify these isomorphism classes with the characters counted by the statement.
  let f (i : s) : defectZeroCharacters 2 A₅ := by
    let V := (Irr.repBundle A₅ i).1
    haveI : Simple V := (Irr.repBundle A₅ i).2
    refine ⟨Irr.charFun A₅ i, V, inferInstance, inferInstance, inferInstance, V.ρ,
      irreducible_of_simple_fdrep A₅ V, Irr.charFun_repBundle A₅ i, ?_⟩
    rw [two_part_card]
    exact (Finset.mem_filter.mp i.property).2
  have hf : Function.Bijective f := by
    refine ⟨fun _ _ e => Subtype.ext (Irr.charFun_inj A₅ (congrArg Subtype.val e)), ?_⟩
    rintro ⟨χ, V, hV, hM, hfin, ρ, hirr, rfl, hdiv⟩
    let i : Irr A₅ := Quotient.mk _ ⟨FDRep.of ρ, simple_fdrep_of_irreducible A₅ ρ⟩
    have hχ : Irr.charFun A₅ i = ρ.character := rfl
    have hd : d i = Module.finrank ℂ V := by
      exact_mod_cast (hcast i).symm.trans ((congrFun hχ 1).trans ρ.char_one)
    refine ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, rfl⟩
    rwa [hd, ← two_part_card]
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simpa using hs

/--
**Kourovka Problem 12.80(b) has a negative answer.** It is not true that for every prime $p$ and
every finite simple group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$.

B. Sambale's counterexample: in $A_5$ with $p = 2$ there is one irreducible character of $2$-defect
zero (the character of degree $4$, so one $2$-block of defect zero) but three classes, those of
$(123)$, $(12345)$ and $(13524)$, with an odd number of solutions of $[x, y] = g$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale,
letter of 5 May 2021 (part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G =
ℤ_3 × S_3; (b) p = 2, G = A_5: one 2-block of defect zero, three classes ((123), (12345), (13524))
with an odd number of solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem simpleDefectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ simpleDefectZeroBlocksEqNondivisibleClasses := by
  intro h
  have he := h 2 Nat.prime_two A₅ (alternatingGroup.isSimpleGroup (by simp))
    (by rw [card_group]; decide)
  rw [character_count, class_count] at he
  contradiction

/--
**Kourovka Problem 12.80(a) has a negative answer.** It is not true that for every prime $p$ and
every finite group $G$ whose order is divisible by $p$, the number of irreducible complex characters
of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an element $g$
for which the number of pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$ is not
divisible by $p$.

L. Barker's counterexample: for $p = 2$ and $G = \mathbb{Z}_3 \times S_3$ there are three
irreducible characters of degree $2$, all of $2$-defect zero (so three $2$-blocks of defect zero),
but only one class, that of $(1, (123))$, with an odd number of solutions of $[x, y] = g$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale,
letter of 5 May 2021 (part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G =
ℤ_3 × S_3; (b) p = 2, G = A_5: one 2-block of defect zero, three classes ((123), (12345), (13524))
with an odd number of solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem defectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ defectZeroBlocksEqNondivisibleClasses := by
  intro h
  apply simpleDefectZeroBlocksEqNondivisibleClasses_refuted
  intro p hp G _ _ _ hdiv
  exact h p hp G hdiv

end MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted
