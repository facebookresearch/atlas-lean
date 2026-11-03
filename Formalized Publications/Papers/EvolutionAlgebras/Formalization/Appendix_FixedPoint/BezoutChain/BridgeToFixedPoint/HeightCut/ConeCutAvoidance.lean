/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationSemiring
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MkSystemBridge
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Find

/-!
# R-B3: last-rung cone-cut avoidance at `n = 3`

Formalizes direction (iii') (§4):
rung-2 avoidance `(bridgeSystem 3 K c hn) 2 ∉ Q` for `Q ∈ Min(J₂)`, from
`(hexp, hN, htower, hcomm, [IsAlgClosed K])` — no `horth`, no diagonality.

## Route

For `Q ∈ Min(J₂)` with contra-hypothesis `G₂ ∈ Q`, the cone-cut shows
`V(Q + (z))` contains a nonzero point `a`; then `F_k(a^x) = 0` for all three
forms, so `v = coordVec b a^x ≠ 0` squares to zero, against `hN`.

## Residual register (exact)

Proved here: PIT cap `height(Q) ≤ 2` (§1), quotient-dimension
`dim(R/Q) ≥ 2` (§2), weak-Nullstellensatz nonemptiness (§4b), `V ⊋ {0}` from
the height cut (§6), the `hN` contradiction (§7), and end-to-end assembly.

* `R1 (properness)`: `Q ⊔ (z) ≠ ⊤` for `Q ∈ Min(J₂)` — proved here
  (`hproper_homog`): the homogeneous core `homCore Q` is prime
  (`homCore_prime`), so minimality forces `Q = homCore Q` (homogeneous);
  a homogeneous prime is contained in the irrelevant ideal
  (`homogPrime_le_span_X`), which is proper.
* `R2 (PIT-cut, CORRECTED direction)`: `height(P') ≤ 3` for
  `P' ∈ Min(Q ⊔ (z))` — needs going-down for the normalization
  `A ⊆ R/Q` (valid since the poly base `A` is normal, Matsumura Thm 9.4),
  not going-up (which proves the reverse contraction inequality); thread
  as `hcut`.

Conditional on exactly `[hcut]` (standard, sketched above).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ConeCutAvoidance

open scoped BigOperators

/-- The homogenizing variable `z = X_last` at `n = 3` (4 variables). -/
noncomputable def zVar (K : Type*) [Field K] :
    MvPolynomial (Fin (statementIndex 3 + 2)) K :=
  MvPolynomial.X (Fin.last (statementIndex 3 + 1))

#print axioms zVar

/-- Cancellation for `WithBot ℕ∞`: from `h + d = ↑N` and `h ≤ ↑k` with
`k + m = N`, conclude `↑m ≤ d`. Both sides are lifted to `ℕ∞` (all cases
with `⊤`/`⊥` contradict finiteness of `↑N`) and `ENat` cancels `↑k`. -/
theorem dim_ge_of_height_add_dim_eq (h d : WithBot ℕ∞) (k m N : ℕ)
    (hN : k + m = N)
    (hcat : h + d = ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞))
    (hle : h ≤ ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞)) :
    ((((m : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤ d := by
  have hNbot : ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞) ≠ ⊥ := WithBot.coe_ne_bot
  have hNtop : ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞) ≠ ⊤ := by
    intro hcon
    have h2 : (⊤ : WithBot ℕ∞) = ((((N : ℕ)) : ℕ∞) : WithBot ℕ∞) := hcon.symm
    rw [WithBot.top_eq_coe] at h2
    exact ENat.natCast_ne_top _ h2.symm
  cases h with
  | bot =>
      rw [WithBot.bot_add] at hcat
      exact (hNbot hcat.symm).elim
  | coe h' =>
      cases d with
      | bot =>
          rw [WithBot.add_bot] at hcat
          exact (hNbot hcat.symm).elim
      | coe d' =>
          rw [← WithBot.coe_add, WithBot.coe_eq_coe] at hcat
          rw [WithBot.coe_le_coe] at hle
          rw [WithBot.coe_le_coe]
          have hN' : ((N : ℕ) : ℕ∞) = ((k : ℕ) : ℕ∞) + ((m : ℕ) : ℕ∞) := by
            rw [← hN, Nat.cast_add]
          rw [hN'] at hcat
          have hle2 : ((k : ℕ) : ℕ∞) + ((m : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) + d' := by
            rw [← hcat]
            exact add_le_add_left hle d'
          exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp hle2

#print axioms dim_ge_of_height_add_dim_eq

/-! ## §1. PIT cap: `height(Q) ≤ 2` -/

/-- Finset of stage generators below rung `j`: image of `bridgeSystem` over
`{k | k.val < j.val}` as a finset (for the `spanRank` bound). -/
noncomputable def stageGens (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) :
    Finset (MvPolynomial (Fin (statementIndex 3 + 2)) K) := by
  classical
  exact Finset.image (bridgeSystem 3 K c hn)
    (Finset.filter (fun k => k.val < j.val) Finset.univ)

#print axioms stageGens

/-- The stage ideal is the span of `stageGens`. -/
theorem stageIdeal_eq_span_stageGens (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) :
    MinAvoidRungs.stageIdeal 3 K c hn j =
      Ideal.span ((stageGens K c hn j) :
        Set (MvPolynomial (Fin (statementIndex 3 + 2)) K)) := by
  classical
  have hF : ((Finset.filter
        (fun k : Fin (statementIndex 3 + 1) => k.val < j.val)
        Finset.univ) :
      Set (Fin (statementIndex 3 + 1))) =
      {k : Fin (statementIndex 3 + 1) | k.val < j.val} := by
    ext k
    rw [Finset.mem_coe, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  unfold MinAvoidRungs.stageIdeal stageGens
  rw [Finset.coe_image, hF]

#print axioms stageIdeal_eq_span_stageGens

/-- Below rung `j` with `j.val = 2` there are at most 2 stage generators. -/
theorem stageGens_card_le_two (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2) :
    (stageGens K c hn j).card ≤ 2 := by
  classical
  set a : Fin (statementIndex 3 + 1) := ⟨0, by decide⟩ with ha
  set b : Fin (statementIndex 3 + 1) := ⟨1, by decide⟩ with hb
  have hne : a ∉ ({b} : Finset (Fin (statementIndex 3 + 1))) := by
    simp only [Finset.mem_singleton]
    rw [ha, hb]
    decide
  have hsub : Finset.filter (fun k => k.val < j.val) Finset.univ ⊆ {a, b} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [hj] at hk
    have h02 : k.val = 0 ∨ k.val = 1 := by omega
    rcases h02 with h0 | h1
    · left
      rw [Fin.ext_iff, ha]
      simpa using h0
    · right
      rw [Fin.ext_iff, hb]
      simpa using h1
  unfold stageGens
  refine le_trans Finset.card_image_le ?_
  refine le_trans (Finset.card_le_card hsub) ?_
  have hcard : ({a, b} : Finset (Fin (statementIndex 3 + 1))).card = 2 := by
    simp [Finset.card_insert_of_notMem hne]
  omega

#print axioms stageGens_card_le_two

/-- PIT cap (§1): `height(Q) ≤ 2` for `Q ∈ Min(J₂)` at rung `j`,
`j.val = 2` — Krull's height theorem plus the 2-generator `spanRank` bound. -/
theorem height_stageMin_le_two (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2)
    (Q : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hQ : Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes) :
    Q.height ≤ ((2 : ℕ) : ℕ∞) := by
  have hPIT := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes
    (MinAvoidRungs.stageIdeal 3 K c hn j) Q hQ
  have hspan : Submodule.span (MvPolynomial (Fin (statementIndex 3 + 2)) K)
        ((stageGens K c hn j) :
          Set (MvPolynomial (Fin (statementIndex 3 + 2)) K))
      = MinAvoidRungs.stageIdeal 3 K c hn j :=
    (stageIdeal_eq_span_stageGens K c hn j).symm
  have hmid : (MinAvoidRungs.stageIdeal 3 K c hn j).spanRank.toENat
      ≤ (((stageGens K c hn j).card : ℕ) : ℕ∞) := by
    rw [Submodule.spanRank_toENat_eq_iInf_finset_card]
    exact iInf_le _ (⟨stageGens K c hn j, hspan⟩ :
      {s : Finset (MvPolynomial (Fin (statementIndex 3 + 2)) K) //
        Submodule.span (MvPolynomial (Fin (statementIndex 3 + 2)) K)
          ((s : Set (MvPolynomial (Fin (statementIndex 3 + 2)) K)))
          = MinAvoidRungs.stageIdeal 3 K c hn j})
  refine le_trans hPIT (le_trans hmid ?_)
  have hc := stageGens_card_le_two K c hn j hj
  exact_mod_cast hc

#print axioms height_stageMin_le_two

/-! ## §2. Quotient dimension: `dim(R/Q) ≥ 2` -/

/-- Quotient dimension (§2): `dim(R/Q) ≥ 2` from the PIT cap, via the
unconditional catenary equality `height + dim = 4` in 4 variables. -/
theorem quot_dim_ge_two (K : Type*) [Field K] [IsAlgClosed K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2)
    (Q : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hQ : Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes) :
    ((((2 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ Q) := by
  have hprime : Q.IsPrime := hQ.isPrime
  have h1 := height_stageMin_le_two K c hn j hj Q hQ
  have hlow := @hlow_uncond 2 K _ _ Q hprime
  have hcat := @mvPolynomial_catenary_eq_of_lower_bound K _
    (statementIndex 3 + 2) Q hprime hlow
  have hN : statementIndex 3 + 2 = 4 := by decide
  have hle : ((Q.height : WithBot ℕ∞)) ≤ ((((2 : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h1
  have hcat' : ((Q.height : WithBot ℕ∞)) +
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ Q)
      = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    have hRHS : (((statementIndex 3 + 2 : ℕ)) : WithBot ℕ∞)
        = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      rw [hN]
      exact (WithBot.coe_natCast 4).symm
    rw [hRHS] at hcat
    exact hcat
  exact dim_ge_of_height_add_dim_eq _ _ 2 2 4 rfl hcat' hle

#print axioms quot_dim_ge_two

/-! ## §4. Weak Nullstellensatz consequence -/

/-- Weak Nullstellensatz (§4b): the zero locus of a proper ideal is
nonempty — via `vanishingIdeal_zeroLocus_eq_radical` and
`radical_eq_top`. -/
theorem zeroLocus_nonempty_of_ne_top (K : Type*) [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hI : I ≠ ⊤) :
    MvPolynomial.zeroLocus K I ≠ ∅ := by
  intro hempty
  have hvan := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I
  rw [hempty] at hvan
  rw [MvPolynomial.vanishingIdeal_empty] at hvan
  have htop : I.radical = ⊤ := hvan.symm
  rw [Ideal.radical_eq_top] at htop
  exact hI htop

#print axioms zeroLocus_nonempty_of_ne_top

/-- The vanishing ideal of the origin is maximal (Mathlib instance). -/
theorem isMaximal_vanishingIdeal_singleton_zero (K : Type*) [Field K] :
    (MvPolynomial.vanishingIdeal K
      ({0} : Set (Fin (statementIndex 3 + 2) → K)) :
      Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K)).IsMaximal :=
  inferInstance

#print axioms isMaximal_vanishingIdeal_singleton_zero

/-! ## §6. The cone cut leaves `V ⊋ {0}` -/

/-- Dimension of a cut component (§6a): `dim(R/P') ≥ 1` from
`height(P') ≤ 3`, via the catenary equality `height + dim = 4`. -/
theorem quot_dim_ge_one_of_height_le_three (K : Type*) [Field K] [IsAlgClosed K]
    (P' : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    [P'.IsPrime] (h3 : P'.height ≤ ((3 : ℕ) : ℕ∞)) :
    ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ P') := by
  have hprime : P'.IsPrime := inferInstance
  have hlow := @hlow_uncond 2 K _ _ P' hprime
  have hcat := @mvPolynomial_catenary_eq_of_lower_bound K _
    (statementIndex 3 + 2) P' hprime hlow
  have hN : statementIndex 3 + 2 = 4 := by decide
  have hle : ((P'.height : WithBot ℕ∞)) ≤ ((((3 : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h3
  have hcat' : ((P'.height : WithBot ℕ∞)) +
      ringKrullDim (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ P')
      = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    have hRHS : (((statementIndex 3 + 2 : ℕ)) : WithBot ℕ∞)
        = ((((4 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      rw [hN]
      exact (WithBot.coe_natCast 4).symm
    rw [hRHS] at hcat
    exact hcat
  have h31 : 3 + 1 = 4 := rfl
  exact dim_ge_of_height_add_dim_eq _ _ 3 1 4 h31 hcat' hle

#print axioms quot_dim_ge_one_of_height_le_three

/-- No cut component is the origin (§6b): if `V(P') = {0}` then `P'` is the
irrelevant maximal ideal, of height 4 — against `height(P') ≤ 3`. -/
theorem zeroLocus_ne_singleton_zero_of_height_le_three (K : Type*) [Field K]
    [IsAlgClosed K]
    (P' : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    [P'.IsPrime] (h3 : P'.height ≤ ((3 : ℕ) : ℕ∞)) :
    MvPolynomial.zeroLocus K P' ≠ {0} := by
  intro hcon
  have hprime : P'.IsPrime := inferInstance
  have hP' : P' = (MvPolynomial.vanishingIdeal K
      ({0} : Set (Fin (statementIndex 3 + 2) → K)) :
      Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K)) := by
    have hvan := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) P'
    rw [hcon] at hvan
    have hrad : P'.radical = P' := hprime.radical
    rw [hrad] at hvan
    exact hvan.symm
  have hmax : P'.IsMaximal := by
    rw [hP']
    exact isMaximal_vanishingIdeal_singleton_zero K
  have h4 := @height_maximal_ge 2 K _ _ P' hmax
  have hle : ((((2 + 2 : ℕ))) : ℕ∞) ≤ ((((3 : ℕ))) : ℕ∞) := le_trans h4 h3
  have h43 : ¬ ((((2 + 2 : ℕ))) : ℕ∞) ≤ ((((3 : ℕ))) : ℕ∞) := by
    intro h
    have hnm : 2 + 2 ≤ 3 := by exact_mod_cast h
    omega
  exact absurd hle h43

#print axioms zeroLocus_ne_singleton_zero_of_height_le_three

/-- The cone cut produces a nonzero point (§6c): from `P' ∈ Min(Q + (z))`
with `height(P') ≤ 3`, get `a ∈ V(Q + (z))`, `a ≠ 0`. -/
theorem exists_ne_zero_mem_zeroLocus_of_height_le_three (K : Type*) [Field K]
    [IsAlgClosed K]
    (Q P' : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hP' : P' ∈ (Q ⊔ Ideal.span {zVar K}).minimalPrimes)
    (h3 : P'.height ≤ ((3 : ℕ) : ℕ∞)) :
    ∃ a ∈ MvPolynomial.zeroLocus K (Q ⊔ Ideal.span {zVar K}), a ≠ 0 := by
  have hprime : P'.IsPrime := hP'.isPrime
  have hne : MvPolynomial.zeroLocus K P' ≠ ∅ := by
    apply zeroLocus_nonempty_of_ne_top K P'
    exact hprime.ne_top
  have hns : MvPolynomial.zeroLocus K P' ≠ {0} :=
    @zeroLocus_ne_singleton_zero_of_height_le_three K _ _ P' hprime h3
  have hex : ∃ a ∈ MvPolynomial.zeroLocus K P', a ≠ 0 := by
    by_contra hall
    have hall : ∀ a ∈ MvPolynomial.zeroLocus K P', a = 0 := by
      intro a ha
      by_contra hne'
      exact hall ⟨a, ha, hne'⟩
    have hsub : MvPolynomial.zeroLocus K P' ⊆ {0} := by
      intro a ha
      simp only [Set.mem_singleton_iff]
      exact hall a ha
    have hsup : ({0} : Set (Fin (statementIndex 3 + 2) → K)) ⊆
        MvPolynomial.zeroLocus K P' := by
      intro a ha
      simp only [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hb0 := hall b hb
      rw [← hb0]
      exact hb
    exact hns (Set.Subset.antisymm hsub hsup)
  obtain ⟨a, haP', hane⟩ := hex
  refine ⟨a, ?_, hane⟩
  exact MvPolynomial.zeroLocus_anti_mono hP'.le haP'

#print axioms exists_ne_zero_mem_zeroLocus_of_height_le_three

/-! ## §7. The `hN` contradiction -/

/-- Reindexing helper: `sqCoords` over shifted constants equals `sqCoords`
over `c` after transporting the point along `shiftEquiv` (both sums
reindexed by `Fintype.sum_equiv`). -/
theorem sqCoords_shiftConsts (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (Y : Fin (statementIndex n + 1) → K)
    (k' : Fin n) :
    CoordinatizationSemiring.sqCoords K c k'
        (fun m => Y ((shiftEquiv n hn).symm m))
      = CoordinatizationSemiring.sqCoords K (shiftConsts n K c hn)
        ((shiftEquiv n hn).symm k') Y := by
  set e := shiftEquiv n hn with he
  have hX : ∀ i, Y (e.symm (e i)) = Y i := fun i => by rw [Equiv.symm_apply_apply]
  have hk' : e (e.symm k') = k' := Equiv.apply_symm_apply e k'
  simp only [CoordinatizationSemiring.sqCoords, shiftConsts, ← he, hk']
  refine (Fintype.sum_equiv (M := K) e _ _ ?_).symm
  intro i
  refine Fintype.sum_equiv (M := K) e _ _ ?_
  intro j
  simp only [hX]

#print axioms sqCoords_shiftConsts

/-- The `hN` contradiction (§7, general `n`): a nonzero point `a` with
`z(a) = 0` on which all of `bridgeSystem` vanishes yields a nonzero
nilpotent vector of `V`, against `hN`. -/
theorem hN_contra_of_cone_point (n : ℕ) (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (V : Submodule K E)
    (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (hn : 0 < n)
    (a : Fin (statementIndex n + 2) → K) (ha0 : a ≠ 0)
    (hz : a (Fin.last (statementIndex n + 1)) = 0)
    (hG : ∀ k : Fin (statementIndex n + 1),
      MvPolynomial.eval a ((bridgeSystem n K c hn) k) = 0) :
    False := by
  set Y : Fin (statementIndex n + 1) → K :=
    fun j => a (Fin.castSucc j) with hY
  have hY0 : Y ≠ 0 := by
    intro hcon
    apply ha0
    funext i
    by_cases hi : i = Fin.last (statementIndex n + 1)
    · subst hi
      simpa using hz
    · obtain ⟨j, rfl⟩ :=
        Fin.eq_castSucc_of_ne_last (n := statementIndex n + 1) hi
      have hj := congrFun hcon j
      simpa [hY] using hj
  have hF : ∀ k : Fin (statementIndex n + 1),
      MvPolynomial.eval Y ((bridgeForms n K c hn) k) = 0 := by
    intro k
    have hk := hG k
    have hk2 : MvPolynomial.eval a
        (mkSystem (statementIndex n) K
          (bridgeForms n K c hn) k) = 0 := hk
    have hsplit := bridgeSystem_eval
      (statementIndex n) K
      (bridgeForms n K c hn) k a
    rw [hsplit, hz] at hk2
    simpa [hY] using hk2
  set X : Fin n → K :=
    fun m => Y ((shiftEquiv n hn).symm m) with hXdef
  have hX0 : X ≠ 0 := by
    intro hcon
    apply hY0
    funext i
    have hi := congrFun hcon ((shiftEquiv n hn) i)
    simpa [hXdef] using hi
  have hsq : ∀ k' : Fin n, CoordinatizationSemiring.sqCoords K c k' X = 0 := by
    intro k'
    have hkk := hF ((shiftEquiv n hn).symm k')
    have heval := eval_mkQuadForm
      (statementIndex n + 1) K
      (shiftConsts n K c hn)
      ((shiftEquiv n hn).symm k') Y
    have hkk2 : CoordinatizationSemiring.sqCoords K
        (shiftConsts n K c hn)
        ((shiftEquiv n hn).symm k') Y = 0 := by
      have hkk' : MvPolynomial.eval Y
          (mkQuadForm (statementIndex n + 1) K
            (shiftConsts n K c hn)
            ((shiftEquiv n hn).symm k')) = 0 := hkk
      rw [heval] at hkk'
      exact hkk'
    have htrans := sqCoords_shiftConsts n K c hn Y k'
    rw [← hXdef] at htrans
    rw [htrans]
    exact hkk2
  set v : E := CoordinatizationSemiring.coordVec K E b X with hv
  have hvV : v ∈ V := by
    rw [hv]
    exact CoordinatizationSemiring.coordVec_mem K E b X
  have hvsq : v * v = 0 := by
    have hexp2 := CoordinatizationSemiring.sq_expand K E b c hexp X
    simp only [hsq, zero_smul, Finset.sum_const_zero] at hexp2
    rw [hv]
    exact hexp2
  have hv0 : v ≠ 0 := by
    intro hcon
    apply hX0
    have hcz : CoordinatizationSemiring.coordVec K E b X = 0 := by
      rw [← hv]
      exact hcon
    exact CoordinatizationSemiring.coordVec_eq_zero K E b X hcz
  have hvend : v = 0 := CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN hvV hvsq
  exact hv0 hvend

#print axioms hN_contra_of_cone_point

/-! ## §3–4. Homogeneous core and properness (`R1`)

The homogeneous core `homCore P` (all homogeneous components lie in `P`)
is an ideal (via the product expansion `hc_mul_expand`) and is prime
when `P` is (`homCore_prime`, via least-nonmember-degree + prime
splitting). Since `J₂` is homogeneous (`stageIdeal2_homog_mem`),
minimality forces `Q = homCore Q`; a homogeneous prime lies in the
irrelevant ideal (`homogPrime_le_span_X`), so `Q ⊔ (z) ≠ ⊤`. -/

/-- `hc` of a product of homogeneous polynomials is product-or-zero. -/
theorem hc_of_homog_mul {σ : Type*} {K : Type*} [Field K]
    {a b k : ℕ} {g h : MvPolynomial σ K}
    (hg : g.IsHomogeneous a) (hh : h.IsHomogeneous b) :
    MvPolynomial.homogeneousComponent k (g * h) =
      if k = a + b then g * h else 0 := by
  have hgh : (g * h).IsHomogeneous (a + b) :=
    MvPolynomial.IsHomogeneous.mul hg hh
  have hmem : g * h ∈ MvPolynomial.homogeneousSubmodule σ K (a + b) :=
    (MvPolynomial.mem_homogeneousSubmodule (a + b) (g * h)).mpr hgh
  exact MvPolynomial.homogeneousComponent_of_mem hmem

#print axioms hc_of_homog_mul

/-- Expansion of `hc` of a product over `range ×ˢ range`. -/
theorem hc_mul_expand {σ : Type*} {K : Type*} [Field K]
    (u v : MvPolynomial σ K) (k : ℕ) :
    MvPolynomial.homogeneousComponent k (u * v) =
      ∑ p ∈ Finset.range (u.totalDegree + 1) ×ˢ Finset.range (v.totalDegree + 1),
        (if k = p.1 + p.2 then
          MvPolynomial.homogeneousComponent p.1 u * MvPolynomial.homogeneousComponent p.2 v
        else 0) := by
  have hu := MvPolynomial.sum_homogeneousComponent u
  have hv := MvPolynomial.sum_homogeneousComponent v
  have euv : u * v = (∑ i ∈ Finset.range (u.totalDegree + 1),
        MvPolynomial.homogeneousComponent i u) *
      (∑ j ∈ Finset.range (v.totalDegree + 1),
        MvPolynomial.homogeneousComponent j v) := by rw [hu, hv]
  rw [euv, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  have aux : ∀ a b, MvPolynomial.homogeneousComponent k
        (MvPolynomial.homogeneousComponent a u * MvPolynomial.homogeneousComponent b v) =
        (if k = a + b then MvPolynomial.homogeneousComponent a u *
          MvPolynomial.homogeneousComponent b v else 0) := fun a b =>
    hc_of_homog_mul (MvPolynomial.homogeneousComponent_isHomogeneous a u)
      (MvPolynomial.homogeneousComponent_isHomogeneous b v)
  simp only [aux]
  rw [← Finset.sum_product']

#print axioms hc_mul_expand

/-- The homogeneous core: polynomials all of whose homogeneous components
lie in `P`. -/
def homCore {σ : Type*} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial σ K) where
  carrier := {x | ∀ i, MvPolynomial.homogeneousComponent i x ∈ P}
  zero_mem' := by
    intro i
    rw [map_zero]
    exact P.zero_mem
  add_mem' := by
    intro a b ha hb i
    rw [map_add]
    exact P.add_mem (ha i) (hb i)
  smul_mem' := by
    intro r x hx i
    rw [smul_eq_mul, hc_mul_expand r x i]
    exact Ideal.sum_mem P (fun p _hp => by
      change (if i = p.1 + p.2 then MvPolynomial.homogeneousComponent p.1 r *
          MvPolynomial.homogeneousComponent p.2 x else
          (0 : MvPolynomial σ K)) ∈ P
      by_cases hif : i = p.1 + p.2
      · rw [ite_eq_left hif]
        exact Ideal.mul_mem_left P _ (hx p.2)
      · rw [ite_eq_right hif]
        exact P.zero_mem)

#print axioms homCore

/-- The homogeneous core lies in `P` (reassemble via `sum_hc`). -/
theorem homCore_le {σ : Type*} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) : homCore P ≤ P := by
  intro x hx
  have hsum := MvPolynomial.sum_homogeneousComponent x
  rw [← hsum]
  exact Ideal.sum_mem P (fun i _hi => hx i)

#print axioms homCore_le

/-- The homogeneous core of a prime is prime: `1 ∉ homCore` since
`hc 0 1 = 1`; for `x * y ∈ homCore` with `x, y ∉ homCore`, take least
nonmember degrees `d, e` and split `hc (d+e) (x*y)` at `(d,e)` — the
off term is a product of nonmembers, the rest lies in `P`. -/
theorem homCore_prime {σ : Type*} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) (hprime : P.IsPrime) :
    (homCore P).IsPrime := by
  classical
  refine ⟨?_, ?_⟩
  · intro hcon
    have h1 : (1 : MvPolynomial σ K) ∈ homCore P := by
      rw [hcon]
      exact Submodule.mem_top
    have h0 : MvPolynomial.homogeneousComponent 0 (1 : MvPolynomial σ K) ∈ P := h1 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0
    rw [MvPolynomial.coeff_one] at h0
    have hif : (if 0 = (0 : σ →₀ ℕ) then (1 : K) else 0) = 1 := ite_eq_left rfl
    rw [hif, MvPolynomial.C_1] at h0
    exact hprime.one_notMem h0
  · intro x y hxy
    by_contra hcon
    have hx : x ∉ homCore P := fun h => hcon (Or.inl h)
    have hy : y ∉ homCore P := fun h => hcon (Or.inr h)
    have hxe : ∃ i, MvPolynomial.homogeneousComponent i x ∉ P := by
      by_contra hall
      apply hx
      intro i
      by_contra hi
      exact hall ⟨i, hi⟩
    have hye : ∃ j, MvPolynomial.homogeneousComponent j y ∉ P := by
      by_contra hall
      apply hy
      intro j
      by_contra hj
      exact hall ⟨j, hj⟩
    set d := Nat.find hxe
    set e := Nat.find hye
    have hd : MvPolynomial.homogeneousComponent d x ∉ P := Nat.find_spec hxe
    have he : MvPolynomial.homogeneousComponent e y ∉ P := Nat.find_spec hye
    have hmem := hxy (d + e)
    rw [hc_mul_expand x y (d + e)] at hmem
    have hdxne : MvPolynomial.homogeneousComponent d x ≠ 0 :=
      fun h => hd (by rw [h]; exact P.zero_mem)
    have heyne : MvPolynomial.homogeneousComponent e y ≠ 0 :=
      fun h => he (by rw [h]; exact P.zero_mem)
    have hdmem : d ∈ Finset.range (x.totalDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp (fun hlt =>
        hdxne (MvPolynomial.homogeneousComponent_eq_zero d x hlt))))
    have hemem : e ∈ Finset.range (y.totalDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp (fun hlt =>
        heyne (MvPolynomial.homogeneousComponent_eq_zero e y hlt))))
    have hde := Finset.mk_mem_product hdmem hemem
    rw [← Finset.add_sum_erase _ _ hde] at hmem
    have hTde : (if d + e = (d, e).1 + (d, e).2 then
          MvPolynomial.homogeneousComponent (d, e).1 x *
            MvPolynomial.homogeneousComponent (d, e).2 y
          else (0 : MvPolynomial σ K))
        = MvPolynomial.homogeneousComponent d x * MvPolynomial.homogeneousComponent e y :=
      ite_eq_left rfl
    rw [hTde] at hmem
    have hTmem : MvPolynomial.homogeneousComponent d x *
        MvPolynomial.homogeneousComponent e y ∈ P := by
      refine (Ideal.add_mem_iff_left P ?_).mp hmem
      apply Ideal.sum_mem
      intro p hp
      rw [Finset.mem_erase] at hp
      have hne := hp.1
      change (if d + e = p.1 + p.2 then MvPolynomial.homogeneousComponent p.1 x *
          MvPolynomial.homogeneousComponent p.2 y else
          (0 : MvPolynomial σ K)) ∈ P
      by_cases hif : d + e = p.1 + p.2
      · rw [ite_eq_left hif]
        have hlt : p.1 < d ∨ p.2 < e := by
          by_contra hc2
          have h1 : ¬ p.1 < d := fun h => hc2 (Or.inl h)
          have h2 : ¬ p.2 < e := fun h => hc2 (Or.inr h)
          have hge1 : d ≤ p.1 := not_lt.mp h1
          have hge2 : e ≤ p.2 := not_lt.mp h2
          have heq1 : p.1 = d := by omega
          have heq2 : p.2 = e := by omega
          exact hne (Prod.ext_iff.mpr ⟨heq1, heq2⟩)
        rcases hlt with hlt | hlt
        · have hmem1 : MvPolynomial.homogeneousComponent p.1 x ∈ P :=
            Classical.byContradiction (Nat.find_min hxe hlt)
          rw [mul_comm]
          exact Ideal.mul_mem_left P _ hmem1
        · have hmem2 : MvPolynomial.homogeneousComponent p.2 y ∈ P :=
            Classical.byContradiction (Nat.find_min hye hlt)
          exact Ideal.mul_mem_left P _ hmem2
      · rw [ite_eq_right hif]
        exact P.zero_mem
    have hor := hprime.mem_or_mem hTmem
    rcases hor with h | h
    · exact hd h
    · exact he h

#print axioms homCore_prime

/-- `J₂` is homogeneous: every component of a member is a member
(`span_induction` with universal motive; generators are homogeneous of
degree 2). -/
theorem stageIdeal2_homog_mem (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) :
    ∀ x ∈ MinAvoidRungs.stageIdeal 3 K c hn j, ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ MinAvoidRungs.stageIdeal 3 K c hn j := by
  intro x hx
  have hx' : x ∈ Submodule.span (MvPolynomial (Fin (statementIndex 3 + 2)) K)
      (Set.image (bridgeSystem 3 K c hn) {k | k.val < j.val}) := hx
  refine Submodule.span_induction (p := fun x _ => ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ MinAvoidRungs.stageIdeal 3 K c hn j) ?_ ?_ ?_ ?_ hx'
  · intro y hy
    show ∀ i, MvPolynomial.homogeneousComponent i y ∈ MinAvoidRungs.stageIdeal 3 K c hn j
    intro i
    obtain ⟨k, hk, rfl⟩ := hy
    have hhom : ((bridgeSystem 3 K c hn) k).IsHomogeneous 2 :=
      bridgeSystem_homogeneous 3 K c hn k
    have hmem2 : (bridgeSystem 3 K c hn) k ∈
        MvPolynomial.homogeneousSubmodule (Fin (statementIndex 3 + 2)) K 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 ((bridgeSystem 3 K c hn) k)).mpr hhom
    have hif : MvPolynomial.homogeneousComponent i ((bridgeSystem 3 K c hn) k) =
        (if i = 2 then (bridgeSystem 3 K c hn) k else 0) :=
      MvPolynomial.homogeneousComponent_of_mem hmem2
    rw [hif]
    by_cases hii : i = 2
    · rw [ite_eq_left hii]
      exact Ideal.subset_span ⟨k, hk, rfl⟩
    · rw [ite_eq_right hii]
      exact (MinAvoidRungs.stageIdeal 3 K c hn j).zero_mem
  · change ∀ i, MvPolynomial.homogeneousComponent i
        (0 : MvPolynomial (Fin (statementIndex 3 + 2)) K) ∈
        MinAvoidRungs.stageIdeal 3 K c hn j
    intro i
    rw [map_zero]
    exact (MinAvoidRungs.stageIdeal 3 K c hn j).zero_mem
  · intro a b _ha _hb iha ihb
    change ∀ i, MvPolynomial.homogeneousComponent i (a + b) ∈
      MinAvoidRungs.stageIdeal 3 K c hn j
    intro i
    rw [map_add]
    exact (MinAvoidRungs.stageIdeal 3 K c hn j).add_mem (iha i) (ihb i)
  · intro r y _hy ih
    change ∀ i, MvPolynomial.homogeneousComponent i (r • y) ∈
      MinAvoidRungs.stageIdeal 3 K c hn j
    intro i
    rw [smul_eq_mul, hc_mul_expand r y i]
    exact Ideal.sum_mem (MinAvoidRungs.stageIdeal 3 K c hn j) (fun p _hp => by
      change (if i = p.1 + p.2 then MvPolynomial.homogeneousComponent p.1 r *
          MvPolynomial.homogeneousComponent p.2 y else
          (0 : MvPolynomial (Fin (statementIndex 3 + 2)) K)) ∈
          MinAvoidRungs.stageIdeal 3 K c hn j
      by_cases hif : i = p.1 + p.2
      · rw [ite_eq_left hif]
        exact Ideal.mul_mem_left (MinAvoidRungs.stageIdeal 3 K c hn j) _ (ih p.2)
      · rw [ite_eq_right hif]
        exact (MinAvoidRungs.stageIdeal 3 K c hn j).zero_mem)

#print axioms stageIdeal2_homog_mem

/-- A homogeneous prime lies in the irrelevant ideal: every support
monomial has a nonzero component, else the constant term would be a unit
in `Q`. -/
theorem homogPrime_le_span_X {σ : Type*} {K : Type*} [Field K]
    (Q : Ideal (MvPolynomial σ K)) (hprime : Q.IsPrime)
    (hhom : ∀ x ∈ Q, ∀ i, MvPolynomial.homogeneousComponent i x ∈ Q) :
    Q ≤ Ideal.span (MvPolynomial.X '' Set.univ) := by
  intro x hx
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hall
  have hm0 : ∀ i, m i = 0 := by
    intro i
    by_contra hi
    exact hall ⟨i, Set.mem_univ i, hi⟩
  have hmeq : m = 0 := Finsupp.ext fun i => (hm0 i).trans Finsupp.zero_apply.symm
  have hcoeff : x.coeff 0 ≠ 0 := by
    rw [← hmeq]
    exact MvPolynomial.mem_support_iff.mp hm
  have hC : MvPolynomial.C (x.coeff 0) ∈ Q := by
    have h0mem : MvPolynomial.homogeneousComponent 0 x ∈ Q := hhom x hx 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0mem
    exact h0mem
  have h1Q : (1 : MvPolynomial σ K) ∈ Q := by
    have hmul : MvPolynomial.C (x.coeff 0) * MvPolynomial.C (x.coeff 0)⁻¹ ∈ Q := by
      rw [mul_comm]
      exact Ideal.mul_mem_left Q _ hC
    have heq : (MvPolynomial.C (x.coeff 0) * MvPolynomial.C (x.coeff 0)⁻¹ :
        MvPolynomial σ K) = 1 := by
      rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hcoeff, MvPolynomial.C_1]
    rw [heq] at hmul
    exact hmul
  exact hprime.one_notMem h1Q

#print axioms homogPrime_le_span_X

/-- Properness `R1`: `Q ⊔ (z) ≠ ⊤` for `Q ∈ Min(J₂)` — minimality forces
`Q = homCore Q`, hence `Q` is homogeneous, hence below the proper
irrelevant ideal. -/
theorem hproper_homog (K : Type*) [Field K]
    (c : Fin 3 → Fin 3 → Fin 3 → K) (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex 3 + 2)) K))
    (hQ : Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes) :
    Q ⊔ Ideal.span {zVar K} ≠ ⊤ := by
  have hprime : Q.IsPrime := hQ.isPrime
  have hmin : (MinAvoidRungs.stageIdeal 3 K c hn j).IsMinimalPrime Q := hQ
  have hHCprime : (homCore Q).IsPrime := homCore_prime Q hprime
  have hHCQ : homCore Q ≤ Q := homCore_le Q
  have hJ₂HC : MinAvoidRungs.stageIdeal 3 K c hn j ≤ homCore Q := by
    intro x hx i
    exact hQ.le (stageIdeal2_homog_mem K c hn j x hx i)
  obtain ⟨_unused, hmin2⟩ := hmin
  have hQleHC : Q ≤ homCore Q := hmin2 ⟨hHCprime, hJ₂HC⟩ hHCQ
  have hHeq : homCore Q = Q := le_antisymm hHCQ hQleHC
  have hQhom : ∀ x ∈ Q, ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ Q := by
    intro x hx i
    have hxHC : x ∈ homCore Q := by
      rw [hHeq]
      exact hx
    exact hxHC i
  have hQsub : Q ≤ Ideal.span (MvPolynomial.X '' Set.univ) :=
    homogPrime_le_span_X Q hprime hQhom
  have h1notin : (1 : MvPolynomial (Fin (statementIndex 3 + 2)) K) ∉
      Ideal.span (MvPolynomial.X '' Set.univ) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro hall
    have h0mem : (0 : Fin (statementIndex 3 + 2) →₀ ℕ) ∈
        (1 : MvPolynomial (Fin (statementIndex 3 + 2)) K).support := by
      rw [MvPolynomial.support_one]
      exact Finset.mem_singleton_self 0
    obtain ⟨i, _univ, hi⟩ := hall 0 h0mem
    rw [Finsupp.zero_apply] at hi
    exact hi rfl
  have hspan_ne : Ideal.span (MvPolynomial.X '' Set.univ :
      Set (MvPolynomial (Fin (statementIndex 3 + 2)) K)) ≠ ⊤ :=
    (Ideal.ne_top_iff_one _).mpr h1notin
  have hle : Q ⊔ Ideal.span {zVar K} ≤
      Ideal.span (MvPolynomial.X '' Set.univ) := by
    refine sup_le hQsub ?_
    refine Ideal.span_le.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    unfold zVar
    exact Ideal.subset_span
      ⟨Fin.last (statementIndex 3 + 1), Set.mem_univ _, rfl⟩
  intro hcon
  rw [hcon] at hle
  exact hspan_ne (top_le_iff.mp hle)

#print axioms hproper_homog

/-! ## Main: rung-2 avoidance at `n = 3` -/

/-- R-B3 cone-cut avoidance (conditional on `[hproper, hcut]`): `G₂ ∉ Q`
for every `Q ∈ Min(J₂)` at rung `j`, `j.val = 2`. Residual `R1`
(`hproper`, from homogeneous-minimal-primes) and `R2` (`hcut`, the
PIT-cut via going-down) are standard; see the module docstring. -/
theorem minAvoidRung_two_of_proper_of_cut (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E] [IsAlgClosed K]
    (V : Submodule K E)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2)
    (hproper : ∀ Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes,
      Q ⊔ Ideal.span {zVar K} ≠ ⊤)
    (hcut : ∀ Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes,
      ∀ P' ∈ (Q ⊔ Ideal.span {zVar K}).minimalPrimes,
        P'.height ≤ ((3 : ℕ) : ℕ∞)) :
    MinAvoidRungs.MinAvoidRung 3 K c hn j := by
  intro Q hQ
  by_contra hcon
  have hne := hproper Q hQ
  obtain ⟨P', hP'⟩ := Ideal.nonempty_minimalPrimes hne
  have h3 := hcut Q hQ P' hP'
  obtain ⟨a, haV, hane⟩ :=
    exists_ne_zero_mem_zeroLocus_of_height_le_three K Q P' hP' h3
  have hz : a (Fin.last (statementIndex 3 + 1)) = 0 := by
    have hmem : zVar K ∈ Q ⊔ Ideal.span {zVar K} :=
      Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (zVar K)))
    have ha0 := haV
    rw [MvPolynomial.mem_zeroLocus_iff] at ha0
    have heval := ha0 (zVar K) hmem
    unfold zVar at heval
    rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X] at heval
    exact heval
  have hGall : ∀ k : Fin (statementIndex 3 + 1),
      MvPolynomial.eval a ((bridgeSystem 3 K c hn) k) = 0 := by
    intro k
    have ha0 := haV
    rw [MvPolynomial.mem_zeroLocus_iff] at ha0
    have hmemQ : (bridgeSystem 3 K c hn) k ∈ Q := by
      by_cases hk : k.val < j.val
      · have hleJ : MinAvoidRungs.stageIdeal 3 K c hn j ≤ Q := hQ.le
        exact hleJ (Ideal.subset_span ⟨k, hk, rfl⟩)
      · have hlt3 : k.val < 3 := by
          have h := k.isLt
          have e : statementIndex 3 + 1 = 3 := by decide
          omega
        have hk2 : k.val = 2 := by omega
        have hkj : k = j := by
          apply Fin.ext
          rw [hk2, hj]
        rw [hkj]
        exact hcon
    have hmemSup : (bridgeSystem 3 K c hn) k ∈
        Q ⊔ Ideal.span {zVar K} := Ideal.mem_sup_left hmemQ
    have hev := ha0 _ hmemSup
    rw [MvPolynomial.aeval_eq_eval] at hev
    exact hev
  exact hN_contra_of_cone_point 3 K E V c b hexp hN hn a hane hz hGall

#print axioms minAvoidRung_two_of_proper_of_cut

/-- R-B3 cone-cut avoidance (conditional on `[hcut]` only): `G₂ ∉ Q`
for every `Q ∈ Min(J₂)` at rung `j`, `j.val = 2`. Residual `R1`
is closed by `hproper_homog`; residual `R2` (`hcut`, the PIT-cut via
going-down) is standard; see the module docstring. -/
theorem minAvoidRung_two_of_cut (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E] [IsAlgClosed K]
    (V : Submodule K E)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (hn : 0 < 3)
    (j : Fin (statementIndex 3 + 1)) (hj : j.val = 2)
    (hcut : ∀ Q ∈ (MinAvoidRungs.stageIdeal 3 K c hn j).minimalPrimes,
      ∀ P' ∈ (Q ⊔ Ideal.span {zVar K}).minimalPrimes,
        P'.height ≤ ((3 : ℕ) : ℕ∞)) :
    MinAvoidRungs.MinAvoidRung 3 K c hn j :=
  minAvoidRung_two_of_proper_of_cut K E V c b hexp hN hn j hj
    (fun Q hQ => hproper_homog K c hn j Q hQ) hcut

#print axioms minAvoidRung_two_of_cut

end ConeCutAvoidance
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
