/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.PermutationBilinearTitsStabilization
public import MathlibExt.GroupTheory.PermutationSchurCocycle
public import MathlibExt.GroupTheory.PermutationBilinearSchurTitsCocycle
public import MathlibExt.GroupTheory.NormalizedCocycleExtension

/-!
# Stabilization of Schur-Tits monomial extensions

Finite permutation stabilization preserves the Schur cocycle and its versions
with two-torsion coefficients. For a skew bicharacter, an element whose square
is one and a two-torsion coefficient, these identities construct an injective
stabilization homomorphism of Schur-Tits monomial extensions, compatible with
the base, coefficient and coefficient-change maps.
-/

@[expose] public section

open PermutationBilinearCocycle
open PermutationBilinearTitsAction
open PermutationBilinearTitsStabilization
open PermutationSchurCocycle
open PermutationBilinearSchurTitsCocycle

universe uA uB

namespace PermutationBilinearSchurStabilization

variable {A : Type uA} [CommGroup A]
variable {B : Type uB} [AddCommGroup B]

section RootEmbedding

variable {n : ℕ}

/-- Embedding of `Root n` into `Root (n+1)` via `Fin.castSucc`. -/
private def rootSuccEmbed (r : Root n) : Root (n + 1) :=
  ⟨(Fin.castSucc r.1.1, Fin.castSucc r.1.2),
    Fin.castSucc_lt_castSucc_iff.mpr r.2⟩

private theorem rootSuccEmbed_val (r : Root n) :
    (rootSuccEmbed (n := n) r).1 = (Fin.castSucc r.1.1, Fin.castSucc r.1.2) := rfl

private theorem rootSuccEmbed_injective {n : ℕ} :
    Function.Injective (rootSuccEmbed (n := n)) := by
  intro r1 r2 h
  apply Subtype.ext
  have h1 := congrArg Subtype.val h
  simp only [rootSuccEmbed_val] at h1
  have h1' : (Fin.castSucc r1.1.1, Fin.castSucc r1.1.2) =
      (Fin.castSucc r2.1.1, Fin.castSucc r2.1.2) := h1
  have ha : Fin.castSucc r1.1.1 = Fin.castSucc r2.1.1 := congrArg Prod.fst h1'
  have hb : Fin.castSucc r1.1.2 = Fin.castSucc r2.1.2 := congrArg Prod.snd h1'
  exact Prod.ext (Fin.castSucc_injective _ ha) (Fin.castSucc_injective _ hb)

private def complRoot (i : Fin n) : Root (n + 1) :=
  ⟨(Fin.castSucc i, Fin.last n),
    Fin.castSucc_lt_last i⟩

private theorem complRoot_val (i : Fin n) :
    (complRoot (n := n) i).1 = (Fin.castSucc i, Fin.last n) := rfl

private theorem rootSuccEmbed_ne_compl {n : ℕ} (r : Root n) (i : Fin n) :
    rootSuccEmbed (n := n) r ≠ complRoot (n := n) i := by
  intro h
  have hv := congrArg Subtype.val h
  simp only [rootSuccEmbed_val, complRoot_val] at hv
  have hb : Fin.castSucc r.1.2 = Fin.last n := congrArg Prod.snd hv
  have hlt : Fin.castSucc r.1.2 < Fin.last n := Fin.castSucc_lt_last r.1.2
  rw [hb] at hlt
  exact lt_irrefl _ hlt

private theorem isOld_iff_second_ne_last (r : Root (n + 1)) :
    (∃ s : Root n, rootSuccEmbed s = r) ↔ r.1.2 ≠ Fin.last n := by
  constructor
  · rintro ⟨s, rfl⟩
    simp only [rootSuccEmbed_val, ne_eq]
    intro h_eq
    have hlt : Fin.castSucc s.1.2 < Fin.last n := Fin.castSucc_lt_last s.1.2
    rw [h_eq] at hlt
    exact lt_irrefl _ hlt
  · intro h_ne
    have hb_ne : r.1.2 ≠ Fin.last n := h_ne
    have hr_lt : r.1.1 < r.1.2 := r.2
    have hb_lt_last : r.1.2 < Fin.last n := by
      apply lt_of_le_of_ne (Fin.le_last _)
      exact hb_ne
    have ha_lt_last : r.1.1 < Fin.last n := lt_trans hr_lt hb_lt_last
    have ha_ne : r.1.1 ≠ Fin.last n := ne_of_lt ha_lt_last
    let a0 : Fin n := Fin.castPred r.1.1 ha_ne
    let b0 : Fin n := Fin.castPred r.1.2 hb_ne
    have ha_eq : Fin.castSucc a0 = r.1.1 := by simp [a0]
    have hb_eq : Fin.castSucc b0 = r.1.2 := by simp [b0]
    have hab : a0 < b0 := by
      have h_cast : Fin.castSucc a0 < Fin.castSucc b0 := by
        rw [ha_eq, hb_eq]
        exact hr_lt
      exact Fin.castSucc_lt_castSucc_iff.mp h_cast
    refine ⟨⟨(a0, b0), hab⟩, ?_⟩
    apply Subtype.ext
    change (Fin.castSucc a0, Fin.castSucc b0) = r.1
    exact Prod.ext ha_eq hb_eq

private theorem complRoot_injective {n : ℕ} :
    Function.Injective (complRoot (n := n)) := by
  intro i j h
  have hv := congrArg Subtype.val h
  simp only [complRoot_val] at hv
  have ha : Fin.castSucc i = Fin.castSucc j := congrArg Prod.fst hv
  exact Fin.castSucc_injective _ ha

private theorem min_castSucc_eq {n : ℕ} (a b : Fin n) :
    min (Fin.castSucc a) (Fin.castSucc (n := n) b) = Fin.castSucc (min a b) := by
  by_cases h : a ≤ b
  · have h' : Fin.castSucc a ≤ Fin.castSucc b := Fin.castSucc_le_castSucc_iff.mpr h
    rw [min_eq_left h, min_eq_left h']
  · have h' : ¬ Fin.castSucc a ≤ Fin.castSucc b := by
      intro hle
      exact h (Fin.castSucc_le_castSucc_iff.mp hle)
    rw [min_eq_right (le_of_not_ge h), min_eq_right (le_of_not_ge h')]

private theorem max_castSucc_eq {n : ℕ} (a b : Fin n) :
    max (Fin.castSucc a) (Fin.castSucc (n := n) b) = Fin.castSucc (max a b) := by
  by_cases h : a ≤ b
  · have h' : Fin.castSucc a ≤ Fin.castSucc b := Fin.castSucc_le_castSucc_iff.mpr h
    rw [max_eq_right h, max_eq_right h']
  · have h' : ¬ Fin.castSucc a ≤ Fin.castSucc b := by
      intro hle
      exact h (Fin.castSucc_le_castSucc_iff.mp hle)
    rw [max_eq_left (le_of_not_ge h), max_eq_left (le_of_not_ge h')]

private theorem rootSuccEmbed_le_iff {n : ℕ} (r1 r2 : Root n) :
    rootSuccEmbed (n := n) r1 ≤ rootSuccEmbed (n := n) r2 ↔ r1 ≤ r2 := by
  have h_eq : (rootSuccEmbed r1 ≤ rootSuccEmbed r2 ↔
      toLex (rootSuccEmbed r1).1 ≤ toLex (rootSuccEmbed r2).1) := Iff.rfl
  have h_eq2 : (r1 ≤ r2 ↔ toLex r1.1 ≤ toLex r2.1) := Iff.rfl
  rw [h_eq, h_eq2]
  rw [show (rootSuccEmbed r1).1 = (Fin.castSucc r1.1.1, Fin.castSucc r1.1.2) from rfl]
  rw [show (rootSuccEmbed r2).1 = (Fin.castSucc r2.1.1, Fin.castSucc r2.1.2) from rfl]
  rw [Prod.Lex.toLex_le_toLex]
  rw [Prod.Lex.toLex_le_toLex]
  constructor
  · intro h
    rcases h with h1 | ⟨heq, h2⟩
    · left
      exact Fin.castSucc_lt_castSucc_iff.mp h1
    · right
      constructor
      · exact Fin.castSucc_injective n heq
      · exact Fin.castSucc_le_castSucc_iff.mp h2
  · intro h
    rcases h with h1 | ⟨heq, h2⟩
    · left
      exact Fin.castSucc_lt_castSucc_iff.mpr h1
    · right
      constructor
      · exact congrArg Fin.castSucc heq
      · exact Fin.castSucc_le_castSucc_iff.mpr h2

private theorem rootSuccEmbed_lt_iff {n : ℕ} (r1 r2 : Root n) :
    rootSuccEmbed (n := n) r1 < rootSuccEmbed (n := n) r2 ↔ r1 < r2 := by
  have h_eq : (rootSuccEmbed r1 < rootSuccEmbed r2 ↔
      toLex (rootSuccEmbed r1).1 < toLex (rootSuccEmbed r2).1) := Iff.rfl
  have h_eq2 : (r1 < r2 ↔ toLex r1.1 < toLex r2.1) := Iff.rfl
  rw [h_eq, h_eq2]
  rw [show (rootSuccEmbed r1).1 = (Fin.castSucc r1.1.1, Fin.castSucc r1.1.2) from rfl]
  rw [show (rootSuccEmbed r2).1 = (Fin.castSucc r2.1.1, Fin.castSucc r2.1.2) from rfl]
  rw [Prod.Lex.toLex_lt_toLex]
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · intro h
    rcases h with h1 | ⟨heq, h2⟩
    · left
      exact Fin.castSucc_lt_castSucc_iff.mp h1
    · right
      constructor
      · exact Fin.castSucc_injective _ heq
      · exact Fin.castSucc_lt_castSucc_iff.mp h2
  · intro h
    rcases h with h1 | ⟨heq, h2⟩
    · left
      exact Fin.castSucc_lt_castSucc_iff.mpr h1
    · right
      constructor
      · exact congrArg Fin.castSucc heq
      · exact Fin.castSucc_lt_castSucc_iff.mpr h2

end RootEmbedding

section PermRootPreservation

variable {n : ℕ} (p : Equiv.Perm (Fin n))

private theorem rootPerm_succ_embed (r : Root n) :
    rootPerm (permSuccHom (n := n) p) (rootSuccEmbed r) =
      rootSuccEmbed (rootPerm p r) := by
  apply Subtype.ext
  simp only [rootPerm_apply, rootSuccEmbed_val,
    permSuccHom_apply_castSucc, mkRoot,
    min_castSucc_eq, max_castSucc_eq]
  apply Prod.ext <;> rfl

private theorem rootPerm_succ_compl (i : Fin n) :
    rootPerm (permSuccHom (n := n) p) (complRoot i) =
      complRoot (p i) := by
  apply Subtype.ext
  simp only [rootPerm_apply, complRoot_val,
    permSuccHom_apply_castSucc, permSuccHom_apply_last, mkRoot,
    min_eq_left (Fin.castSucc_lt_last (p i)).le,
    max_eq_right (Fin.castSucc_lt_last (p i)).le]

end PermRootPreservation

section SignBitPreservation

variable {n : ℕ} (p : Equiv.Perm (Fin n))

private theorem rootSignBit_succ_embed (r : Root n) :
    rootSignBit (permSuccHom (n := n) p) (rootSuccEmbed r) =
      rootSignBit p r := by
  unfold rootSignBit
  have h_inv1 : (permSuccHom (n := n) p)⁻¹ (Fin.castSucc r.1.1) =
      Fin.castSucc ((p⁻¹) r.1.1) := by
    have h_eq : (permSuccHom (n := n) p)⁻¹ = permSuccHom (n := n) p⁻¹ :=
      permSuccHom_inv p
    rw [h_eq, permSuccHom_apply_castSucc]
  have h_inv2 : (permSuccHom (n := n) p)⁻¹ (Fin.castSucc r.1.2) =
      Fin.castSucc ((p⁻¹) r.1.2) := by
    have h_eq : (permSuccHom (n := n) p)⁻¹ = permSuccHom (n := n) p⁻¹ :=
      permSuccHom_inv p
    rw [h_eq, permSuccHom_apply_castSucc]
  have h_iff : ((permSuccHom p)⁻¹ (Fin.castSucc r.1.1) <
      (permSuccHom p)⁻¹ (Fin.castSucc r.1.2) ↔
      p⁻¹ r.1.1 < p⁻¹ r.1.2) := by
    rw [h_inv1, h_inv2, Fin.castSucc_lt_castSucc_iff]
  have h_val : (rootSuccEmbed (n := n) r).1.1 = Fin.castSucc r.1.1 := rfl
  have h_val2 : (rootSuccEmbed (n := n) r).1.2 = Fin.castSucc r.1.2 := rfl
  rw [h_val, h_val2]
  by_cases h : p⁻¹ r.1.1 < p⁻¹ r.1.2
  · have h' : (permSuccHom p)⁻¹ (Fin.castSucc r.1.1) <
        (permSuccHom p)⁻¹ (Fin.castSucc r.1.2) := h_iff.mpr h
    simp only [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ (permSuccHom p)⁻¹ (Fin.castSucc r.1.1) <
        (permSuccHom p)⁻¹ (Fin.castSucc r.1.2) := fun hh => h (h_iff.mp hh)
    simp only [ite_eq_right h, ite_eq_right h']

private theorem rootSignBit_succ_compl (i : Fin n) :
    rootSignBit (permSuccHom (n := n) p) (complRoot i) = 0 := by
  unfold rootSignBit
  have h_inv1 : (permSuccHom (n := n) p)⁻¹ (Fin.castSucc i) =
      Fin.castSucc ((p⁻¹) i) := by
    have h_eq : (permSuccHom (n := n) p)⁻¹ = permSuccHom (n := n) p⁻¹ :=
      permSuccHom_inv p
    rw [h_eq, permSuccHom_apply_castSucc]
  have h_inv2 : (permSuccHom (n := n) p)⁻¹ (Fin.last n) = Fin.last n := by
    have h_eq : (permSuccHom (n := n) p)⁻¹ = permSuccHom (n := n) p⁻¹ :=
      permSuccHom_inv p
    rw [h_eq, permSuccHom_apply_last]
  have h_lt : (permSuccHom p)⁻¹ (Fin.castSucc i) < (permSuccHom p)⁻¹ (Fin.last n) := by
    rw [h_inv1, h_inv2]
    exact Fin.castSucc_lt_last _
  have h_val1 : (complRoot (n := n) i).1.1 = Fin.castSucc i := rfl
  have h_val2 : (complRoot (n := n) i).1.2 = Fin.last n := rfl
  rw [h_val1, h_val2]
  simp only [ite_eq_left h_lt]

private theorem rootSign_succ_embed (q : Equiv.Perm (Fin n)) (r : Root n) :
    rootSign (permSuccHom (n := n) q) (rootSuccEmbed r) =
      rootSign q r := by
  unfold rootSign
  rw [rootSignBit_succ_embed q r]

private theorem rootSign_succ_compl (q : Equiv.Perm (Fin n)) (i : Fin n) :
    rootSign (permSuccHom (n := n) q) (complRoot i) = 1 := by
  unfold rootSign
  rw [rootSignBit_succ_compl q i]
  rfl

private theorem rootPerm_succ_embed_inv (p : Equiv.Perm (Fin n)) (r : Root n) :
    (rootPerm (permSuccHom (n := n) p))⁻¹ (rootSuccEmbed r) =
      rootSuccEmbed ((rootPerm p)⁻¹ r) := by
  let s : Root n := (rootPerm p)⁻¹ r
  have hs : rootPerm p s = r := by simp [s]
  have h_embed : rootPerm (permSuccHom p) (rootSuccEmbed s) = rootSuccEmbed r := by
    rw [← hs, rootPerm_succ_embed]
  have h_inv : (rootPerm (permSuccHom p))⁻¹ (rootSuccEmbed r) = rootSuccEmbed s := by
    calc (rootPerm (permSuccHom p))⁻¹ (rootSuccEmbed r)
        = (rootPerm (permSuccHom p))⁻¹ ((rootPerm (permSuccHom p)) (rootSuccEmbed s)) := by
          rw [h_embed]
      _ = rootSuccEmbed s := Equiv.symm_apply_apply _ _
  exact h_inv

private theorem permute_rootSign_succ_embed (p q : Equiv.Perm (Fin n)) (r : Root n) :
    permute (rootPerm (permSuccHom (n := n) p)) (rootSign (permSuccHom (n := n) q))
        (rootSuccEmbed r) =
      permute (rootPerm p) (rootSign q) r := by
  simp only [permute_apply]
  have h_inv : (rootPerm (permSuccHom p))⁻¹ (rootSuccEmbed r) =
      rootSuccEmbed ((rootPerm p)⁻¹ r) :=
    rootPerm_succ_embed_inv p r
  rw [h_inv, rootSign_succ_embed]

private theorem permute_rootSign_succ_compl (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    permute (rootPerm (permSuccHom (n := n) p)) (rootSign (permSuccHom (n := n) q))
        (complRoot i) = 1 := by
  simp only [permute_apply]
  have h_inv : (rootPerm (permSuccHom p))⁻¹ = rootPerm (permSuccHom p⁻¹) := by
    rw [← rootPerm_inv, permSuccHom_inv]
  have h_mem : (rootPerm (permSuccHom p))⁻¹ (complRoot i) =
      complRoot ((p⁻¹) i) := by
    rw [h_inv, rootPerm_succ_compl]
  rw [h_mem, rootSign_succ_compl]

end SignBitPreservation

section FinsetPartition

variable {n : ℕ}

private def finsetOld : Finset (Root (n + 1)) :=
  (Finset.univ : Finset (Root n)).map ⟨rootSuccEmbed, rootSuccEmbed_injective⟩

private def finsetCompl : Finset (Root (n + 1)) :=
  (Finset.univ : Finset (Fin n)).map ⟨complRoot, complRoot_injective⟩

private theorem mem_finsetOld {r : Root (n + 1)} :
    r ∈ finsetOld (n := n) ↔ ∃ s : Root n, rootSuccEmbed s = r := by
  simp [finsetOld, Finset.mem_map]

private theorem mem_finsetCompl {r : Root (n + 1)} :
    r ∈ finsetCompl (n := n) ↔ ∃ i : Fin n, complRoot i = r := by
  simp [finsetCompl, Finset.mem_map]

private theorem finsetOld_disjoint_compl :
    Disjoint (finsetOld (n := n)) (finsetCompl (n := n)) := by
  rw [Finset.disjoint_left]
  intro r hr_old hr_compl
  rw [mem_finsetOld] at hr_old
  rw [mem_finsetCompl] at hr_compl
  obtain ⟨s, hs⟩ := hr_old
  obtain ⟨i, hi⟩ := hr_compl
  have h_eq : rootSuccEmbed s = complRoot i := by rw [hs, hi]
  exact absurd h_eq (rootSuccEmbed_ne_compl s i)

private theorem mem_old_iff_ne_last (r : Root (n + 1)) :
    r ∈ finsetOld (n := n) ↔ r.1.2 ≠ Fin.last n := by
  rw [mem_finsetOld, isOld_iff_second_ne_last]

private theorem mem_compl_iff_eq_last (r : Root (n + 1)) :
    r ∈ finsetCompl (n := n) ↔ r.1.2 = Fin.last n := by
  constructor
  · intro h
    rw [mem_finsetCompl] at h
    obtain ⟨i, hi⟩ := h
    rw [← hi, complRoot_val]
  · intro h_eq
    have h_lt : r.1.1 < Fin.last n := by
      have h_lt2 : r.1.1 < r.1.2 := r.2
      rw [h_eq] at h_lt2
      exact h_lt2
    have h_ne_last : r.1.1 ≠ Fin.last n := ne_of_lt h_lt
    let i : Fin n := Fin.castPred r.1.1 h_ne_last
    have hi_eq : Fin.castSucc i = r.1.1 := by simp [i]
    have h_compl : complRoot (n := n) i = r := by
      apply Subtype.ext
      simp only [complRoot_val]
      exact Prod.ext hi_eq h_eq.symm
    rw [mem_finsetCompl]
    exact ⟨i, h_compl⟩

private theorem univ_eq_old_union_compl :
    (Finset.univ : Finset (Root (n + 1))) = finsetOld (n := n) ∪ finsetCompl (n := n) := by
  ext r
  simp only [Finset.mem_univ, Finset.mem_union, true_iff]
  by_cases h : r.1.2 = Fin.last n
  · right
    rw [mem_compl_iff_eq_last]
    exact h
  · left
    rw [mem_old_iff_ne_last]
    exact h

private theorem filter_le_old_map {n : ℕ} (i : Root n) :
    (Finset.univ.filter (fun j' : Root (n + 1) => j' ≤ rootSuccEmbed i)).filter
        (fun j' => j' ∈ finsetOld (n := n)) =
      (Finset.univ.filter (fun j : Root n => j ≤ i)).map
        ⟨rootSuccEmbed, rootSuccEmbed_injective⟩ := by
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨hle, hold⟩
    have h_ne : r'.1.2 ≠ Fin.last n := (mem_old_iff_ne_last r').mp hold
    have h_exists : ∃ s : Root n, rootSuccEmbed s = r' :=
      (isOld_iff_second_ne_last r').mpr h_ne
    obtain ⟨s, hs⟩ := h_exists
    have hle2 : rootSuccEmbed s ≤ rootSuccEmbed i := by
      rw [← hs] at hle
      exact hle
    have hle3 : s ≤ i := (rootSuccEmbed_le_iff s i).mp hle2
    exact ⟨s, hle3, hs⟩
  · rintro ⟨s, hs_le, rfl⟩
    constructor
    · rw [rootSuccEmbed_le_iff]
      exact hs_le
    · rw [mem_finsetOld]
      exact ⟨s, rfl⟩

private theorem filter_lt_old_map {n : ℕ} (i : Root n) :
    (Finset.univ.filter (fun j' : Root (n + 1) => rootSuccEmbed i < j')).filter
        (fun j' => j' ∈ finsetOld (n := n)) =
      (Finset.univ.filter (fun j : Root n => i < j)).map
        ⟨rootSuccEmbed, rootSuccEmbed_injective⟩ := by
  ext r'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨hlt, hold⟩
    have h_ne : r'.1.2 ≠ Fin.last n := (mem_old_iff_ne_last r').mp hold
    have h_exists : ∃ s : Root n, rootSuccEmbed s = r' :=
      (isOld_iff_second_ne_last r').mpr h_ne
    obtain ⟨s, hs⟩ := h_exists
    have hlt2 : rootSuccEmbed i < rootSuccEmbed s := by
      rw [← hs] at hlt
      exact hlt
    have hlt3 : i < s := (rootSuccEmbed_lt_iff i s).mp hlt2
    exact ⟨s, hlt3, hs⟩
  · rintro ⟨s, hs_lt, rfl⟩
    constructor
    · rw [rootSuccEmbed_lt_iff]
      exact hs_lt
    · rw [mem_finsetOld]
      exact ⟨s, rfl⟩

end FinsetPartition

section SumInvariants

variable {n : ℕ}

private theorem lowerSum_rootSucc_aux
    (u : Root n → Multiplicative (ZMod 2))
    (v : Root n → Multiplicative (ZMod 2))
    (u' : Root (n + 1) → Multiplicative (ZMod 2))
    (v' : Root (n + 1) → Multiplicative (ZMod 2))
    (hu_embed : ∀ r : Root n, u' (rootSuccEmbed r) = u r)
    (hu_compl : ∀ i : Fin n, u' (complRoot i) = 1)
    (hv_embed : ∀ r : Root n, v' (rootSuccEmbed r) = v r)
    (hv_compl : ∀ i : Fin n, v' (complRoot i) = 1) :
    lowerSum (ι := Root (n + 1)) bitBicharacter u' v' =
      lowerSum (ι := Root n) bitBicharacter u v := by
  unfold lowerSum
  have h_univ : (Finset.univ : Finset (Root (n + 1))) =
      finsetOld (n := n) ∪ finsetCompl (n := n) := univ_eq_old_union_compl
  -- outer sum: univ = old ∪ compl, compl contributes 0
  have h_outer : (∑ i' : Root (n + 1), ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
        bitBicharacter.eval (u' i') (v' j')) =
      (∑ i' ∈ finsetOld (n := n), ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
        bitBicharacter.eval (u' i') (v' j')) := by
    have h1 : (∑ i' : Root (n + 1), ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
        bitBicharacter.eval (u' i') (v' j')) =
        ∑ i' ∈ (Finset.univ : Finset (Root (n + 1))),
          ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
            bitBicharacter.eval (u' i') (v' j') := rfl
    rw [h1]
    have h_eq : (∑ i' ∈ finsetOld (n := n), ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
        bitBicharacter.eval (u' i') (v' j')) =
        ∑ i' ∈ (Finset.univ : Finset (Root (n + 1))),
          ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
            bitBicharacter.eval (u' i') (v' j') := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i' hi' h_not_old
      have h_compl : i' ∈ finsetCompl (n := n) := by
        have h_mem : i' ∈ (Finset.univ : Finset (Root (n + 1))) := hi'
        have h_union : i' ∈ finsetOld (n := n) ∪ finsetCompl (n := n) := by
          rw [← h_univ]; exact h_mem
        rw [Finset.mem_union] at h_union
        rcases h_union with h_old | h_c
        · exact absurd h_old h_not_old
        · exact h_c
      rw [mem_finsetCompl] at h_compl
      obtain ⟨i, rfl⟩ := h_compl
      have hu : u' (complRoot i) = 1 := hu_compl i
      apply Finset.sum_eq_zero
      intro j' _
      rw [hu]
      simp
    exact h_eq.symm
  rw [h_outer]
  have h_old_eq : (∑ i' ∈ finsetOld (n := n),
        ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ i'),
          bitBicharacter.eval (u' i') (v' j')) =
      ∑ i : Root n, ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i),
          bitBicharacter.eval (u i) (v' j') := by
    rw [finsetOld, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    apply Finset.sum_congr rfl
    intro r _
    rw [hu_embed r]
  rw [h_old_eq]
  apply Finset.sum_congr rfl
  intro i _
  have h_filter_old : (Finset.univ.filter (fun j' : Root (n + 1) => j' ≤ rootSuccEmbed i)).filter
        (fun j' => j' ∈ finsetOld (n := n)) =
      (Finset.univ.filter (fun j : Root n => j ≤ i)).map
        ⟨rootSuccEmbed, rootSuccEmbed_injective⟩ := filter_le_old_map i
  have h_inner : (∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i),
        bitBicharacter.eval (u i) (v' j')) =
      (∑ j' ∈ (Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i)).filter
          (fun j' => j' ∈ finsetOld (n := n)),
        bitBicharacter.eval (u i) (v' j')) := by
    have h_eq : (∑ j' ∈ (Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i)).filter
          (fun j' => j' ∈ finsetOld (n := n)),
        bitBicharacter.eval (u i) (v' j')) =
        ∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i),
          bitBicharacter.eval (u i) (v' j') := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j' hj' hj_not_old
      have hj_compl : j' ∈ finsetCompl (n := n) := by
        have h_mem : j' ∈ (Finset.univ : Finset (Root (n + 1))) :=
          (Finset.mem_filter.mp hj').1
        have h_union : j' ∈ finsetOld (n := n) ∪ finsetCompl (n := n) := by
          rw [← h_univ]; exact Finset.mem_univ _
        rw [Finset.mem_union] at h_union
        rcases h_union with h_old | h_c
        · have h_in_s : j' ∈ (Finset.univ.filter (fun j' => j' ≤ rootSuccEmbed i)).filter
              (fun j' => j' ∈ finsetOld (n := n)) :=
            Finset.mem_filter.mpr ⟨hj', h_old⟩
          exact absurd h_in_s hj_not_old
        · exact h_c
      rw [mem_finsetCompl] at hj_compl
      obtain ⟨k, hk⟩ := hj_compl
      rw [← hk, hv_compl k]
      simp
    exact h_eq.symm
  rw [h_inner, h_filter_old, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  apply Finset.sum_congr rfl
  intro j _
  rw [hv_embed j]

private theorem inversionSum_rootSucc_aux
    (σ : Equiv.Perm (Root n))
    (σ' : Equiv.Perm (Root (n + 1)))
    (u : Root n → Multiplicative (ZMod 2))
    (u' : Root (n + 1) → Multiplicative (ZMod 2))
    (hu_embed : ∀ r : Root n, u' (rootSuccEmbed r) = u r)
    (hu_compl : ∀ i : Fin n, u' (complRoot i) = 1)
    (hσ_embed : ∀ r : Root n, σ' (rootSuccEmbed r) = rootSuccEmbed (σ r))
    (_hσ_compl : ∀ i : Fin n, ∃ j : Fin n, σ' (complRoot i) = complRoot j) :
    inversionSum (ι := Root (n + 1)) bitBicharacter σ' u' =
      inversionSum (ι := Root n) bitBicharacter σ u := by
  unfold inversionSum
  have h_univ : (Finset.univ : Finset (Root (n + 1))) =
      finsetOld (n := n) ∪ finsetCompl (n := n) := univ_eq_old_union_compl
  have h_outer : (∑ i' : Root (n + 1), ∑ j' ∈ Finset.univ.filter
        (fun j' => i' < j' ∧ σ' i' > σ' j'),
        bitBicharacter.eval (u' i') (u' j')) =
      (∑ i' ∈ finsetOld (n := n), ∑ j' ∈ Finset.univ.filter
          (fun j' => i' < j' ∧ σ' i' > σ' j'),
        bitBicharacter.eval (u' i') (u' j')) := by
    have h_eq : (∑ i' ∈ finsetOld (n := n), ∑ j' ∈ Finset.univ.filter
          (fun j' => i' < j' ∧ σ' i' > σ' j'),
        bitBicharacter.eval (u' i') (u' j')) =
        ∑ i' ∈ (Finset.univ : Finset (Root (n + 1))),
          ∑ j' ∈ Finset.univ.filter (fun j' => i' < j' ∧ σ' i' > σ' j'),
            bitBicharacter.eval (u' i') (u' j') := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i' hi' h_not_old
      have h_compl : i' ∈ finsetCompl (n := n) := by
        have h_mem : i' ∈ (Finset.univ : Finset (Root (n + 1))) := hi'
        have h_union : i' ∈ finsetOld (n := n) ∪ finsetCompl (n := n) := by
          rw [← h_univ]; exact h_mem
        rw [Finset.mem_union] at h_union
        rcases h_union with h_old | h_c
        · exact absurd h_old h_not_old
        · exact h_c
      rw [mem_finsetCompl] at h_compl
      obtain ⟨i, rfl⟩ := h_compl
      have hu : u' (complRoot i) = 1 := hu_compl i
      apply Finset.sum_eq_zero
      intro j' _
      rw [hu]
      simp
    exact h_eq.symm
  rw [h_outer]
  have h_old_eq : (∑ i' ∈ finsetOld (n := n),
        ∑ j' ∈ Finset.univ.filter (fun j' => i' < j' ∧ σ' i' > σ' j'),
        bitBicharacter.eval (u' i') (u' j')) =
      ∑ i : Root n, ∑ j' ∈ Finset.univ.filter
          (fun j' => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j'),
        bitBicharacter.eval (u i) (u' j') := by
    rw [finsetOld, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    apply Finset.sum_congr rfl
    intro r _
    rw [hu_embed r]
  rw [h_old_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hσ_embed_i : σ' (rootSuccEmbed i) = rootSuccEmbed (σ i) := hσ_embed i
  have h_filter_old : (Finset.univ.filter
        (fun j' : Root (n + 1) => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j')).filter
        (fun j' => j' ∈ finsetOld (n := n)) =
      (Finset.univ.filter (fun j : Root n => i < j ∧ σ i > σ j)).map
        ⟨rootSuccEmbed, rootSuccEmbed_injective⟩ := by
    ext r'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨⟨hlt, hgt⟩, hold⟩
      have h_ne : r'.1.2 ≠ Fin.last n := (mem_old_iff_ne_last r').mp hold
      have h_exists : ∃ s : Root n, rootSuccEmbed s = r' :=
        (isOld_iff_second_ne_last r').mpr h_ne
      obtain ⟨s, hs⟩ := h_exists
      rw [← hs] at hlt hgt
      rw [rootSuccEmbed_lt_iff] at hlt
      have hgt' : σ i > σ s := by
        have hσ_s : σ' (rootSuccEmbed s) = rootSuccEmbed (σ s) := hσ_embed s
        have hgt_lt : σ' (rootSuccEmbed s) < σ' (rootSuccEmbed i) := hgt
        rw [hσ_s, hσ_embed_i] at hgt_lt
        have h_lt : σ s < σ i := (rootSuccEmbed_lt_iff _ _).mp hgt_lt
        exact h_lt
      exact ⟨s, ⟨hlt, hgt'⟩, hs⟩
    · rintro ⟨s, ⟨hlt, hgt⟩, rfl⟩
      constructor
      · constructor
        · rw [rootSuccEmbed_lt_iff]; exact hlt
        · have hσ_s : σ' (rootSuccEmbed s) = rootSuccEmbed (σ s) := hσ_embed s
          have hgt_lt : σ s < σ i := hgt
          have h_lt : σ' (rootSuccEmbed s) < σ' (rootSuccEmbed i) := by
            rw [hσ_s, hσ_embed_i, rootSuccEmbed_lt_iff]
            exact hgt_lt
          exact h_lt
      · rw [mem_finsetOld]
        exact ⟨s, rfl⟩
  have h_inner : (∑ j' ∈ Finset.univ.filter
        (fun j' => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j'),
        bitBicharacter.eval (u i) (u' j')) =
      (∑ j' ∈ (Finset.univ.filter
          (fun j' => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j')).filter
          (fun j' => j' ∈ finsetOld (n := n)),
        bitBicharacter.eval (u i) (u' j')) := by
    have h_eq : (∑ j' ∈ (Finset.univ.filter
          (fun j' => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j')).filter
          (fun j' => j' ∈ finsetOld (n := n)),
        bitBicharacter.eval (u i) (u' j')) =
        ∑ j' ∈ Finset.univ.filter
          (fun j' => rootSuccEmbed i < j' ∧ σ' (rootSuccEmbed i) > σ' j'),
          bitBicharacter.eval (u i) (u' j') := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j' hj' hj_not_old
      have hj_not_mem_old : j' ∉ finsetOld (n := n) := by
        intro h_old
        exact hj_not_old (Finset.mem_filter.mpr ⟨hj', h_old⟩)
      have hj_compl : j' ∈ finsetCompl (n := n) := by
        have h_mem : j' ∈ (Finset.univ : Finset (Root (n + 1))) :=
          (Finset.mem_filter.mp hj').1
        have h_union : j' ∈ finsetOld (n := n) ∪ finsetCompl (n := n) := by
          rw [← h_univ]; exact Finset.mem_univ _
        rw [Finset.mem_union] at h_union
        rcases h_union with h_old | h_c
        · exact absurd h_old hj_not_mem_old
        · exact h_c
      rw [mem_finsetCompl] at hj_compl
      obtain ⟨k, hk⟩ := hj_compl
      rw [← hk, hu_compl k]
      simp
    exact h_eq.symm
  rw [h_inner, h_filter_old, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  apply Finset.sum_congr rfl
  intro j _
  rw [hu_embed j]

end SumInvariants

section ParityInvariance

variable {n : ℕ}

private theorem parityBit_permSucc (p : Equiv.Perm (Fin n)) :
    parityBit (permSuccHom (n := n) p) = parityBit p := by
  unfold parityBit
  have h := permSuccHom_parityUnit (n := n) (eps := Multiplicative.ofAdd (1 : ZMod 2)) p
  exact congrArg Multiplicative.toAdd h

end ParityInvariance

section SchurCocycleInvariance

variable {n : ℕ}

private theorem rootCocycle0_permSucc (p q : Equiv.Perm (Fin n)) :
    rootCocycle0 (permSuccHom (n := n) p) (permSuccHom (n := n) q) =
      rootCocycle0 p q := by
  have h_rootSign_p : ∀ r : Root n, rootSign (permSuccHom p) (rootSuccEmbed r) = rootSign p r :=
    fun r => rootSign_succ_embed p r
  have h_rootSign_q : ∀ r : Root n, rootSign (permSuccHom q) (rootSuccEmbed r) = rootSign q r :=
    fun r => rootSign_succ_embed q r
  have h_rootSign_p_compl : ∀ i : Fin n, rootSign (permSuccHom p) (complRoot i) = 1 :=
    fun i => rootSign_succ_compl p i
  have h_rootSign_q_compl : ∀ i : Fin n, rootSign (permSuccHom q) (complRoot i) = 1 :=
    fun i => rootSign_succ_compl q i
  have h_perm_p : ∀ r : Root n, (rootPerm (permSuccHom p)) (rootSuccEmbed r) =
      rootSuccEmbed ((rootPerm p) r) := rootPerm_succ_embed p
  have h_perm_p_compl :
      ∀ i : Fin n, ∃ j : Fin n, (rootPerm (permSuccHom p)) (complRoot i) = complRoot j := by
    intro i
    exact ⟨p i, rootPerm_succ_compl p i⟩
  have h_permute_q : ∀ r : Root n,
      permute (rootPerm (permSuccHom p)) (rootSign (permSuccHom q)) (rootSuccEmbed r) =
        permute (rootPerm p) (rootSign q) r :=
    fun r => permute_rootSign_succ_embed p q r
  have h_permute_q_compl : ∀ i : Fin n,
      permute (rootPerm (permSuccHom p)) (rootSign (permSuccHom q)) (complRoot i) = 1 :=
    fun i => permute_rootSign_succ_compl p q i
  have h_lower : lowerSum (ι := Root (n + 1)) bitBicharacter
        (rootSign (permSuccHom p))
        (permute (rootPerm (permSuccHom p)) (rootSign (permSuccHom q))) =
      lowerSum (ι := Root n) bitBicharacter (rootSign p) (permute (rootPerm p) (rootSign q)) := by
    apply lowerSum_rootSucc_aux
    · exact h_rootSign_p
    · exact h_rootSign_p_compl
    · exact h_permute_q
    · exact h_permute_q_compl
  have h_inv : inversionSum (ι := Root (n + 1)) bitBicharacter
        (rootPerm (permSuccHom p)) (rootSign (permSuccHom q)) =
      inversionSum (ι := Root n) bitBicharacter (rootPerm p) (rootSign q) := by
    apply inversionSum_rootSucc_aux
    · exact h_rootSign_q
    · exact h_rootSign_q_compl
    · exact h_perm_p
    · exact h_perm_p_compl
  -- rootCocycle0 p q = lowerSum bitBicharacter (rootSign p) ... + inversionSum ...
  -- expose via unfolding rootMonomial application
  have h_expand_succ : rootCocycle0 (permSuccHom (n := n) p) (permSuccHom (n := n) q) =
      lowerSum bitBicharacter (rootSign (permSuccHom p))
        (permute (rootPerm (permSuccHom p)) (rootSign (permSuccHom q))) +
      inversionSum bitBicharacter (rootPerm (permSuccHom p)) (rootSign (permSuccHom q)) := by
    unfold rootCocycle0
    dsimp [rootMonomial]
  have h_expand : rootCocycle0 (n := n) p q =
      lowerSum bitBicharacter (rootSign p) (permute (rootPerm p) (rootSign q)) +
      inversionSum bitBicharacter (rootPerm p) (rootSign q) := by
    unfold rootCocycle0
    dsimp [rootMonomial]
  rw [h_expand_succ, h_expand, h_lower, h_inv]

theorem schurCocycle_permSucc (p q : Equiv.Perm (Fin n)) :
    schurCocycle (permSuccHom (n := n) p) (permSuccHom (n := n) q) =
      schurCocycle p q := by
  unfold schurCocycle
  rw [rootCocycle0_permSucc, parityBit_permSucc, parityBit_permSucc]

theorem schurCocycleWith_permSucc {A : Type*} [AddCommGroup A]
    (z : A) (hz : 2 • z = 0) (p q : Equiv.Perm (Fin n)) :
    schurCocycleWith (n := n + 1) z hz (permSuccHom p) (permSuccHom q) =
      schurCocycleWith (n := n) z hz p q := by
  unfold schurCocycleWith
  congr 1
  exact schurCocycle_permSucc p q

end SchurCocycleInvariance

section SchurTitsInvariance

variable {n : ℕ} {A : Type uA} [CommGroup A] {B : Type uB} [AddCommGroup B]
variable (b : SkewBicharacter A B) (eps : A) (z : B) (hz : 2 • z = 0)

theorem schurTitsMonomialAddCocycle_monomialSucc (x y : MonomialBase A (Fin n)) :
    schurTitsMonomialAddCocycle (n := n + 1) b eps z hz
        (monomialSuccHom (n := n) x) (monomialSuccHom (n := n) y) =
      schurTitsMonomialAddCocycle (n := n) b eps z hz x y := by
  unfold schurTitsMonomialAddCocycle
  have h_tits := titsMonomialAddCocycle_monomialSucc (n := n) b eps x y
  have h_schur : schurCocycleWith (n := n + 1) z hz
        (monomialSuccHom (n := n) x).right (monomialSuccHom (n := n) y).right =
      schurCocycleWith (n := n) z hz x.right y.right := by
    simp only [monomialSuccHom_right]
    exact schurCocycleWith_permSucc z hz x.right y.right
  rw [h_tits, h_schur]

end SchurTitsInvariance

section CompatibleMapSucc

variable {n : ℕ} {A : Type uA} [CommGroup A] {B : Type uB} [AddCommGroup B]
variable {b : SkewBicharacter A B} {eps : A} (heps : eps * eps = 1)
  {z : B} (hz : 2 • z = 0)

noncomputable def schurTitsSuccCompatibleMap :
    NormalizedCocycleExtension.CompatibleMap
      (schurTitsMonomialNormalizedCocycle (n := n) b eps heps z hz)
      (schurTitsMonomialNormalizedCocycle (n := n + 1) b eps heps z hz) where
  f := monomialSuccHom (n := n) (A := A)
  g := MonoidHom.id (Multiplicative B)
  q := fun _ => 1
  q_one := rfl
  compat x y := by
    simp only [MonoidHom.id_apply, mul_one, one_mul]
    change Multiplicative.ofAdd (schurTitsMonomialAddCocycle (n := n) b eps z hz x y) =
      Multiplicative.ofAdd (schurTitsMonomialAddCocycle (n := n + 1) b eps z hz
        (monomialSuccHom x) (monomialSuccHom y))
    rw [schurTitsMonomialAddCocycle_monomialSucc b eps z hz x y]

noncomputable def schurTitsSuccCompatibleHom :
    SchurTitsMonomialExtension (n := n) b eps heps z hz →*
      SchurTitsMonomialExtension (n := n + 1) b eps heps z hz :=
  (schurTitsSuccCompatibleMap (n := n) heps (z := z) hz).toHom

@[simp]
theorem schurTitsSuccCompatibleHom_base (x : SchurTitsMonomialExtension (n := n) b eps heps z hz) :
    (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz x).base =
      monomialSuccHom (n := n) x.base :=
  rfl

@[simp]
theorem schurTitsSuccCompatibleHom_coeff (x : SchurTitsMonomialExtension (n := n) b eps heps z hz) :
    (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz x).coeff = x.coeff := by
  simp [schurTitsSuccCompatibleHom, schurTitsSuccCompatibleMap]

theorem schurTitsSuccCompatibleHom_injective :
    Function.Injective
      (schurTitsSuccCompatibleHom (n := n) (b := b) (eps := eps) heps (z := z) hz) := by
  intro x y h
  have h_base : (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz x).base =
      (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz y).base := by rw [h]
  have h_coeff : (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz x).coeff =
      (schurTitsSuccCompatibleHom (n := n) heps (z := z) hz y).coeff := by rw [h]
  simp only [schurTitsSuccCompatibleHom_base, schurTitsSuccCompatibleHom_coeff] at h_base h_coeff
  have hx_base : x.base = y.base := monomialSuccHom_injective h_base
  have hx_coeff : x.coeff = y.coeff := h_coeff
  apply NormalizedCocycleExtension.Extension.ext hx_base hx_coeff

theorem schurTitsSuccCompatibleHom_naturality
    {A' : Type*} {B' : Type*} [CommGroup A'] [AddCommGroup B']
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b')
    {eps' : A'} (heps' : φ.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    {z' : B'} (hz' : 2 • z' = 0) (hzmap : φ.target z = z')
    (x : SchurTitsMonomialExtension (n := n) b eps heps z hz) :
    schurTitsMonomialCompatibleHom (n := n + 1) φ heps' hepsA hepsB hz hz' hzmap
        (schurTitsSuccCompatibleHom (n := n) heps hz x) =
      schurTitsSuccCompatibleHom (n := n) hepsB hz'
        (schurTitsMonomialCompatibleHom (n := n) φ heps' hepsA hepsB hz hz' hzmap x) := by
  apply NormalizedCocycleExtension.Extension.ext
  · simp only [schurTitsSuccCompatibleHom_base, schurTitsMonomialCompatibleHom_base,
      monomialSuccHom_skewNaturality]
  · simp only [schurTitsSuccCompatibleHom_coeff, schurTitsMonomialCompatibleHom_coeff]

end CompatibleMapSucc

end PermutationBilinearSchurStabilization

end
