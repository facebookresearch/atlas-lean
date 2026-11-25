/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.Kinship
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import MathlibExt.NumberTheory.BinetClosedForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Inbreeding under repeated full-sib mating

The state consists of within-individual and between-sib probabilities of non-identity by descent
at a single autosomal locus. The model uses fair, independent Mendelian transmissions and no
selection. The two parents have a common within-individual probability at the founding generation;
thereafter the two sexes have the same transmission law. Non-identity is with respect to a fixed
base population, not inequality of allelic states. The recurrence is studied for all pairs in the
unit square, without requiring every such pair to be realized by a pedigree.
-/

@[expose] public section

open Filter Topology

namespace Domains.Biology.PopulationGenetics.Classical.FullSibMating

open MathlibExt.Biology.StatisticalGenetics.Kinship (Pedigree)

/-- **Within- and between-individual non-identity under full-sib mating.** Starting from the
founder probabilities `h₀` and `k₀`, return the pair `(h, k)` at generation `t`. The two copies
within an offspring come from different parents. Two independently drawn copies from different
siblings come from different parents half the time. Otherwise they come from the same parent,
where the two transmitted copies are identical by descent if the same copy was transmitted and
have non-identity probability `h` if distinct copies were transmitted. These two cases are equally
likely conditional on the same parent.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §V.10,
[pp. 234–235](https://felsenst.github.io/pgbook/pgbook.pdf), equations (V-26) and (V-27). -/
noncomputable def nonIdentity (h₀ k₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (h₀, k₀)
  | t + 1 =>
    let (h, k) := nonIdentity h₀ k₀ t
    (k, (h / 2 + k) / 2)

private theorem sib_kinship_of_lt {n : ℕ} (P : Pedigree n) {x y : Fin n}
    {p : Fin 2 → Fin n} (hxy : x < y) (hx : P.parents x = some p) (hy : P.parents y = some p) :
    P.geneDropKinship x y =
      ((P.geneDropKinship (p 0) (p 0) + P.geneDropKinship (p 0) (p 1)) +
        (P.geneDropKinship (p 1) (p 0) + P.geneDropKinship (p 1) (p 1))) / 4 := by
  have hparent (a : Fin 2) : P.geneDropKinship x (p a) =
      (P.geneDropKinship (p a) (p 0) + P.geneDropKinship (p a) (p 1)) / 2 := by
    rw [P.geneDropKinship_comm x (p a)]
    exact P.geneDropKinship_of_parents_eq_some (P.parents_lt x p hx a).ne'
      (fun h ↦ (not_lt_of_ge (P.parents_lt x p hx a).le) h.lt) hx
  rw [P.geneDropKinship_of_parents_eq_some hxy.ne' (fun h ↦ (not_lt_of_ge hxy.le) h.lt) hy,
    hparent, hparent]
  ring

private theorem sib_kinship {n : ℕ} (P : Pedigree n) {x y : Fin n} {p : Fin 2 → Fin n}
    (hxy : x ≠ y) (hx : P.parents x = some p) (hy : P.parents y = some p) :
    P.geneDropKinship x y =
      ((P.geneDropKinship (p 0) (p 0) + P.geneDropKinship (p 0) (p 1)) +
        (P.geneDropKinship (p 1) (p 0) + P.geneDropKinship (p 1) (p 1))) / 4 := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact sib_kinship_of_lt P h hx hy
  · rw [P.geneDropKinship_comm x y]
    exact sib_kinship_of_lt P h hy hx

/-- **Full-sib recurrence in a finite pedigree.** Let `pair t` name the two distinct individuals
at generation `t`, up to generation `T`. The generation-zero pair are founders (not necessarily
siblings), and both individuals at each subsequent generation have the preceding pair as their
parents. Under the gene-dropping law, the within-individual and between-individual probabilities
of non-identity by descent agree with the full-sib recurrence seeded at `(1, 1)`. The within-
individual claim holds for both siblings. This does not require the two siblings' ancestries to
be independent; it uses the fresh transmissions in the pedigree kinship recursion.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019,
[§V.10](https://felsenst.github.io/pgbook/pgbook.pdf), pp. 234–235, equations (V-26) and (V-27).
The finite pedigree convention makes all founder copies distinct. -/
theorem pedigree_nonIdentity {n T : ℕ} (P : Pedigree n) (pair : ℕ → Fin 2 → Fin n)
    (founders : ∀ a, P.parents (pair 0 a) = none)
    (distinct : ∀ t ≤ T, pair t 0 ≠ pair t 1)
    (parents : ∀ t < T, ∀ a, P.parents (pair (t + 1) a) = some (pair t))
    (t : ℕ) (ht : t ≤ T) :
    (∀ a, 1 - P.inbreeding (pair t a) = (nonIdentity 1 1 t).1) ∧
      1 - P.geneDropKinship (pair t 0) (pair t 1) = (nonIdentity 1 1 t).2 := by
  induction t with
  | zero =>
    refine ⟨fun a ↦ ?_, ?_⟩
    · rw [P.inbreeding_of_parents_eq_none (founders a)]
      simp [nonIdentity]
    · have hnot : ¬ P.IsAncestor (pair 0 1) (pair 0 0) := by
        intro h
        cases h with
        | single h => obtain ⟨p, hp, _⟩ := h; simp [founders] at hp
        | tail _ h => obtain ⟨p, hp, _⟩ := h; simp [founders] at hp
      rw [P.geneDropKinship_of_parents_eq_none (distinct 0 ht).symm hnot (founders 1)]
      simp [nonIdentity]
  | succ t ih =>
    have hlt : t < T := ht
    obtain ⟨hwithin, hbetween⟩ := ih hlt.le
    refine ⟨fun a ↦ ?_, ?_⟩
    · rw [P.inbreeding_of_parents_eq_some (parents t hlt a)]
      exact hbetween
    · set h := (nonIdentity 1 1 t).1
      set k := (nonIdentity 1 1 t).2
      change 1 - P.geneDropKinship (pair (t + 1) 0) (pair (t + 1) 1) = (h / 2 + k) / 2
      rw [sib_kinship P (distinct (t + 1) ht) (parents t hlt 0) (parents t hlt 1),
        P.geneDropKinship_self, P.geneDropKinship_self,
        P.geneDropKinship_comm (pair t 1) (pair t 0)]
      linarith [hwithin 0, hwithin 1, hbetween]

/-- **Inbreeding under repeated full-sib mating.** The non-identity probabilities `h` and `k`
remain in `[0, 1]` for any founder values in `[0, 1]`. They satisfy `h (t + 1) = k t` and
`k (t + 1) = h t / 4 + k t / 2`; hence `k` satisfies the corresponding two-generation recurrence.
Writing `lPlus = (1 + √5) / 4` and `lMinus = (1 - √5) / 4`, the solution is
`A * lPlus ^ t + B * lMinus ^ t`, where `A = (k 1 - lMinus * k₀) / (lPlus - lMinus)`
and `B = (lPlus * k₀ - k 1) / (lPlus - lMinus)`.
Here `k 1 = h₀ / 4 + k₀ / 2`. The panmictic index `1 - F` is `h` and tends to zero. If the
founder probabilities are not both zero, then `A > 0`, `k t / lPlus ^ t` tends to `A`, and
`h t / lPlus ^ t` tends to `A / lPlus`, with `0 < lPlus < 1`. For example, starting at `(0, 1)`,
`h` rises from `0` to `1` in the first generation. The convention for non-inbred, unrelated
founders is `h₀ = k₀ = 1`.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019,
[§§V.10–V.11](https://felsenst.github.io/pgbook/pgbook.pdf), equations (V-26)–(V-32) and (V-40).
The exact coefficients and normalized limits refine the source's characteristic-root argument. -/
theorem nonIdentity_formula {h₀ k₀ : ℝ} (hh : h₀ ∈ Set.Icc (0 : ℝ) 1)
    (hk : k₀ ∈ Set.Icc (0 : ℝ) 1) :
    let h := fun t ↦ (nonIdentity h₀ k₀ t).1
    let k := fun t ↦ (nonIdentity h₀ k₀ t).2
    let lPlus : ℝ := (1 + Real.sqrt 5) / 4
    let lMinus : ℝ := (1 - Real.sqrt 5) / 4
    let k₁ := h₀ / 4 + k₀ / 2
    let A := (k₁ - lMinus * k₀) / (lPlus - lMinus)
    let B := (lPlus * k₀ - k₁) / (lPlus - lMinus)
    (∀ t, h t ∈ Set.Icc 0 1 ∧ k t ∈ Set.Icc 0 1) ∧
    (∀ t, h (t + 1) = k t ∧ k (t + 1) = h t / 4 + k t / 2) ∧
    (∀ t, k (t + 2) = k (t + 1) / 2 + k t / 4) ∧
    (lPlus ^ 2 - lPlus / 2 - 1 / 4 = 0 ∧ lMinus ^ 2 - lMinus / 2 - 1 / 4 = 0) ∧
    (0 < lPlus ∧ lPlus < 1 ∧ |lMinus| < lPlus) ∧
    (∀ t, k t = A * lPlus ^ t + B * lMinus ^ t) ∧
    Tendsto h atTop (𝓝 0) ∧
    (h₀ ≠ 0 ∨ k₀ ≠ 0 →
      0 < A ∧ Tendsto (fun t ↦ k t / lPlus ^ t) atTop (𝓝 A) ∧
      Tendsto (fun t ↦ h t / lPlus ^ t) atTop (𝓝 (A / lPlus))) := by
  intro h k lPlus lMinus k₁ A B
  have hzero : h 0 = h₀ := rfl
  have kzero : k 0 = k₀ := rfl
  have hstep (t : ℕ) : h (t + 1) = k t := rfl
  have kstep (t : ℕ) : k (t + 1) = h t / 4 + k t / 2 := by
    change (h t / 2 + k t) / 2 = _
    ring
  have hbounds (t : ℕ) : h t ∈ Set.Icc 0 1 ∧ k t ∈ Set.Icc 0 1 := by
    induction t with
    | zero => exact ⟨hh, hk⟩
    | succ t ih =>
      obtain ⟨⟨hh₀, hh₁⟩, ⟨hk₀, hk₁⟩⟩ := ih
      rw [hstep, kstep]
      exact ⟨⟨hk₀, hk₁⟩, ⟨by linarith, by linarith⟩⟩
  have krec (t : ℕ) : k (t + 2) = k (t + 1) / 2 + k t / 4 := by
    rw [show t + 2 = (t + 1) + 1 from rfl, kstep, hstep, add_comm]
  have hsqrt : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_lo : 1 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsqrt_hi : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hpos : 0 < lPlus := by dsimp [lPlus]; linarith
  have hlt : lPlus < 1 := by dsimp [lPlus]; linarith
  have hneg : lMinus < 0 := by dsimp [lMinus]; linarith
  have habs : |lMinus| < lPlus := by rw [abs_of_neg hneg]; dsimp [lMinus, lPlus]; linarith
  have hgap : 0 < lPlus - lMinus := sub_pos.mpr (hneg.trans hpos)
  have hquadPlus : lPlus ^ 2 - lPlus / 2 - 1 / 4 = 0 := by dsimp [lPlus]; nlinarith
  have hquadMinus : lMinus ^ 2 - lMinus / 2 - 1 / 4 = 0 := by dsimp [lMinus]; nlinarith
  have hk1 : k 1 = k₁ := by
    change k (0 + 1) = _
    rw [kstep, hzero, kzero]
  have hclosed (t : ℕ) : k t = A * lPlus ^ t + B * lMinus ^ t := by
    rw [MetaMathlibExt.binet_closed_form_second_order k (1 / 2) (-1 / 4) lPlus lMinus
      (by linarith) (by linarith) (ne_of_gt (hneg.trans hpos)) (fun n ↦ by rw [krec]; ring) t,
      hk1, kzero]
    dsimp only [A, B]
    ring
  have hk_limit : Tendsto k atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt
    have hm := tendsto_pow_atTop_nhds_zero_iff.mpr (habs.trans hlt)
    simpa using (((hp.const_mul A).add (hm.const_mul B)).congr (fun t ↦ (hclosed t).symm))
  have hh_limit : Tendsto h atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (hk_limit.congr fun t ↦ (hstep t).symm)
  refine ⟨hbounds, fun t ↦ ⟨hstep t, kstep t⟩, krec, ⟨hquadPlus, hquadMinus⟩,
    ⟨hpos, hlt, habs⟩, hclosed, hh_limit, ?_⟩
  intro hnz
  have hA : 0 < A := by
    refine div_pos ?_ hgap
    dsimp only [k₁]
    have hterm := mul_nonpos_of_nonpos_of_nonneg hneg.le hk.1
    rcases hnz with hh' | hk'
    · have hhpos := lt_of_le_of_ne hh.1 hh'.symm
      linarith [hhpos, hk.1]
    · have hkpos := lt_of_le_of_ne hk.1 hk'.symm
      linarith [hh.1, hkpos]
  have hratio : |lMinus / lPlus| < 1 := by
    rwa [abs_div, abs_of_pos hpos, div_lt_one hpos]
  have hq := tendsto_pow_atTop_nhds_zero_iff.mpr hratio
  have hk_normalized : Tendsto (fun t ↦ k t / lPlus ^ t) atTop (𝓝 A) := by
    have hlim := (tendsto_const_nhds (x := A)).add (hq.const_mul B)
    simp only [mul_zero, add_zero] at hlim
    apply hlim.congr
    intro t
    rw [hclosed, div_pow]
    field_simp [pow_ne_zero t hpos.ne']
  refine ⟨hA, hk_normalized, (tendsto_add_atTop_iff_nat 1).mp ?_⟩
  apply (hk_normalized.div_const lPlus).congr
  intro t
  rw [hstep, pow_succ, div_div]

end Domains.Biology.PopulationGenetics.Classical.FullSibMating
