/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ContractionFormula
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The Koszul filtration lift: gr-exactness forces `𝔪 • H = H` (recon option 1)

Closes the file-6 residual `GrLiftFiltrationConseq` (the filtration half of
the gr-lift R2: `K(sop)` exact over `R_P`) modulo two explicit handoffs.
No `Ideal.Filtration` instances and no graded complex are built (by design);
the Artin–Rees index comes straight from `artinRees_submodule`.

* (§1) Shifted pieces `F(t,k) = 𝔪^(t-k) • ⊤` of `⋀^k`, monotone in `t`,
  `= ⊤` for `t ≤ k`, plus the Artin–Rees index on cycles. Unconditional.
* (§2) `d`-preservation: `range φ ⊆ 𝔪` from `gᵢ ∈ 𝔪` and same-exponent
  preservation are unconditional; the shifted preservation
  `d(F(t,k+1)) ⊆ F(t,k)` is conditional-exact on the generator bound
  `FiltrGenBound` (contraction of each `ιMulti` wedge lies in `𝔪 • ⊤`),
  via the spanning-set reduction (proved) + linearity.
* (§3) The single-step lift: `z ∈ Z ∩ F(t)` gives `z = d w + z'` with
  `z' ∈ Z ∩ F(t+1)`, consuming gr-exactness through the leading-term data
  `FiltrLeadData` (hand-built maps stated with intertwining against
  `grlift_phiGr`, kernel control, and lift-back surjectivity). The
  `ιMulti`-spanning extension engine is unconditional (proved); the maps
  themselves are the explicit residual. No AR-free chase is attempted.
* (§4) Iteration to the Artin–Rees index + the homology consequence
  `𝔪 • H = H`, hence `GrLiftFiltrationConseq`. Conditional-exact on
  `[FiltrGenBound, FiltrLeadData]`.

## References

Project (all read-only): `Regularity/Koszul/GradedLift.lean` (§3:
`GrLiftFiltrationConseq`:530, `grlift_exterior_finite`:419,
`grlift_cycles`:396, `grlift_phiGr`:224), `Regularity/Koszul/FiltrationStability.lean`
(`artinRees_submodule`:170, `isNoetherianRing_atPrime`:305),
`Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece_mk_surjective`:119),
`Regularity/Koszul/GradedSurjection.lean` (`genClass`:166),
`Regularity/Koszul/AugmentedConeStep.lean` (`contractExactAt`:61),
`Regularity/Koszul/KoszulComplex.lean` (`contractLeft_ιMulti_mem`:303,
`koszulContract_mem`:329, `koszulContract`:346).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/Filtration.lean`: `Ideal.exists_pow_inf_eq_pow_smul` (:388).
* `RingTheory/Ideal/Operations.lean`: `Ideal.pow_le_pow_right` (:353),
  `Submodule.smul_mono`, `Submodule.map_smul''`, `Submodule.mul_smul`,
  `Submodule.top_smul`, `Submodule.smul_top_le_comap_smul_top` (:1475),
  `Submodule.smul_le_right` (:75).
* `LinearAlgebra/ExteriorPower/Basic.lean`: `exteriorPower.ιMulti_span`
  (:108), `ιMulti_apply_coe` (:60).
* `LinearAlgebra/Quotient/Basic.lean` + `Defs.lean`: `mkQ`, `mk_surjective`,
  `mk_eq_zero`, `range_mkQ`, `range_subtype`, `map_top`.
* `LinearAlgebra/StdBasis.lean`: `Pi.basisFun`; `Module.Basis.sum_repr`,
  `Module.Basis.constr_basis`.

## Status

* §1 + `filtr_phi_mem` + `filtr_map_le_same` + spanning engine: unconditional.
* `filtr_d_preshift`: conditional-exact on `[FiltrGenBound]`.
* `filtr_single_of_lead`, `filtr_iterate`: conditional-exact on
  `[FiltrGenBound, FiltrLeadData]` + gr-exactness.
* `filtr_hconseq_of_lead`, `filtr_grlift_conseq_of_lead`: conditional-exact
  on `[FiltrGenBound, FiltrLeadData]`.
* Residuals (explicit, unproved): `FiltrGenBound` (contraction generator
  bound), `FiltrLeadData` (leading-term maps + intertwining + lift-back).

## Resource knobs (inventoried, permitted class)

`set_option maxSynthPendingDepth 4 in` (scoped) on `filtr_hconseq_of_lead`
and `filtr_grlift_conseq_of_lead`: same knob as file 6 (nested TC for
submodule quotients over a `ker`-of-`koszulContract` ambient exceeds depth 3).
`set_option maxHeartbeats 2000000 in` (scoped) on `filtr_hconseq_of_lead`:
the ~25-tactic homology chase (quotient `Submodule`/`Module` TC + defeq
through exterior-power/`DirectSum` layers at every step) exceeds the default
200000-heartbeat command budget (verified: fails at 1000000, passes at
2000000). Neither is a linter suppression.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FiltrationLift

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

variable {K : Type*} [Field K] {m : ℕ}
  (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
variable (d : ℕ) (g : Fin d → Localization.AtPrime P)

/-- The regular local ring `R_P` (reducible, so instances flow). -/
abbrev FRL : Type _ := Localization.AtPrime P

/-! ## §1. Shifted filtration pieces -/

/-- The shifted piece `F(t,k) = 𝔪^(t-k) • ⊤` of `⋀^k`. -/
noncomputable def filtrPiece (t k : ℕ) :
    Submodule (FRL P) ↥(⋀[FRL P]^k (Fin d → FRL P)) :=
  IsLocalRing.maximalIdeal (FRL P) ^ (t - k) • ⊤

/-- Unfolding equation for `filtrPiece`. -/
theorem filtrPiece_def (t k : ℕ) :
    filtrPiece P d t k = IsLocalRing.maximalIdeal (FRL P) ^ (t - k) • ⊤ :=
  rfl

/-- Below the diagonal the piece is everything. Proved. -/
theorem filtrPiece_eq_top_of_le (t k : ℕ) (h : t ≤ k) :
    filtrPiece P d t k = ⊤ := by
  rw [filtrPiece_def, Nat.sub_eq_zero_of_le h, pow_zero, Ideal.one_eq_top]
  exact Submodule.top_smul _

/-- The Artin–Rees index on cycles: the trace of the adic filtration on
`Zⱼ` stabilizes. Proved (direct from `artinRees_submodule`; finiteness via
`grlift_exterior_finite`, Noetherian via `isNoetherianRing_atPrime`). -/
theorem filtr_ar_index (j : ℕ) :
    ∃ k, ∀ n ≥ k, IsLocalRing.maximalIdeal (FRL P) ^ n • ⊤ ⊓
      grlift_cycles (koszulContractOfSequence g) j =
      IsLocalRing.maximalIdeal (FRL P) ^ (n - k) •
        (IsLocalRing.maximalIdeal (FRL P) ^ k • ⊤ ⊓
          grlift_cycles (koszulContractOfSequence g) j) :=
  artinRees_submodule (IsLocalRing.maximalIdeal (FRL P))
    (grlift_cycles (koszulContractOfSequence g) j)

/-! ## §2. `d`-preservation -/

/-- The Koszul functional takes values in `𝔪`: `φ(m)` is an `R_P`-linear
combination of the `gᵢ ∈ 𝔪`. Proved. -/
theorem filtr_phi_mem
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (x : Fin d → FRL P) :
    koszulContractOfSequence g x ∈ IsLocalRing.maximalIdeal (FRL P) := by
  have hmem : ∀ i : Fin d, g i ∈ IsLocalRing.maximalIdeal (FRL P) := by
    intro i
    have h : g i ∈ Ideal.span (Set.range g) :=
      Submodule.subset_span (Set.mem_range_self i)
    rwa [hgen] at h
  change ((Pi.basisFun (FRL P) (Fin d)).constr (FRL P) g) x ∈
    IsLocalRing.maximalIdeal (FRL P)
  have hsum := (Pi.basisFun (FRL P) (Fin d)).sum_repr x
  rw [← hsum, map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis]
  exact Submodule.smul_mem _ _ (hmem i)

/-- Same-exponent preservation: every `R_P`-linear map sends `𝔪^a • ⊤` into
itself. Proved (needs no `gᵢ ∈ 𝔪`). -/
theorem filtr_map_le_same (a j : ℕ) :
    Submodule.map (koszulContract (koszulContractOfSequence g) j)
        (IsLocalRing.maximalIdeal (FRL P) ^ a • ⊤) ≤
      IsLocalRing.maximalIdeal (FRL P) ^ a • ⊤ :=
  Submodule.map_le_iff_le_comap.mpr
    (Submodule.smul_top_le_comap_smul_top _ _)

/-- Generator bound: contraction of every decomposable wedge lies in
`𝔪 • ⊤`. Residual (the `contractLeft_ι_mul` induction over `ιMulti`,
with coefficients in `𝔪` by `filtr_phi_mem`). -/
def FiltrGenBound : Prop :=
  ∀ (k : ℕ) (v : Fin (k + 1) → (Fin d → FRL P)),
    koszulContract (koszulContractOfSequence g) k
        ⟨ExteriorAlgebra.ιMulti (FRL P) (k + 1) v,
          mem_ιMulti_piece (k + 1) v⟩ ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P) ↥(⋀[FRL P]^k (Fin d → FRL P)))

/-- Shifted preservation `d(F(t,k+1)) ⊆ F(t,k)`. The reduction to the
generator bound (spanning-set check + linearity) is proved;
conditional-exact on `[FiltrGenBound]`. -/
theorem filtr_d_preshift (hGB : FiltrGenBound P d g) (t j : ℕ) :
    Submodule.map (koszulContract (koszulContractOfSequence g) j)
        (filtrPiece P d t (j + 1)) ≤ filtrPiece P d t j := by
  by_cases hle : t ≤ j
  · rw [filtrPiece_eq_top_of_le P d t j hle]
    exact le_top
  · have ha2 : t - j = (t - (j + 1)) + 1 := by omega
    rw [filtrPiece_def, filtrPiece_def, ha2, pow_succ,
      Submodule.mul_smul, Submodule.map_smul'']
    refine Submodule.smul_mono le_rfl ?_
    rw [Submodule.map_top]
    intro z hz
    obtain ⟨y, rfl⟩ := hz
    have hspan := exteriorPower.ιMulti_span (FRL P) (j + 1) (Fin d → FRL P)
    have hy : y ∈ Submodule.span (FRL P)
        (Set.range (exteriorPower.ιMulti (FRL P) (j + 1))) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.span_induction ?mem ?zero ?add ?smul hy
    · intro w hw
      obtain ⟨a, rfl⟩ := hw
      exact hGB j a
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    · intro c x _ ihx
      rw [map_smul]
      exact Submodule.smul_mem _ _ ihx

/-! ## §3. Leading-term data and the single-step lift -/

/-- The `ιMulti` wedges span each exterior power. Proved. -/
theorem filtr_iotaMulti_span (k : ℕ) :
    Submodule.span (FRL P)
        (Set.range (exteriorPower.ιMulti (FRL P) k
          (M := Fin d → FRL P))) = ⊤ :=
  exteriorPower.ιMulti_span (FRL P) k (Fin d → FRL P)

/-- Linearity-extension engine: a predicate holding on `0`, stable under
`+`/`•`, and holding on all `ιMulti` wedges holds everywhere. Proved. -/
theorem filtr_extend_of_iotaMulti {k : ℕ}
    {p : ↥(⋀[FRL P]^k (Fin d → FRL P)) → Prop} (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : FRL P) (x), p x → p (c • x))
    (hgen : ∀ a : Fin k → (Fin d → FRL P),
      p (exteriorPower.ιMulti (FRL P) k a)) (x : ↥(⋀[FRL P]^k (Fin d → FRL P))) :
    p x := by
  have hx : x ∈ Submodule.span (FRL P)
      (Set.range (exteriorPower.ιMulti (FRL P) k
        (M := Fin d → FRL P))) := by
    rw [filtr_iotaMulti_span]
    exact Submodule.mem_top
  refine Submodule.span_induction ?mem ?zero ?add ?smul hx
  · intro w hw
    obtain ⟨a, rfl⟩ := hw
    exact hgen a
  · exact h0
  · intro x y _ _ ihx ihy
    exact hadd x y ihx ihy
  · intro c x _ ihx
    exact hsmul c x ihx

/-- Leading-term data: hand-built maps on the ambient exterior powers
(restricted by membership hypotheses to the filtration pieces), landing in
the gr-side exterior powers, additive on pieces, intertwining `d` with
`grlift_phiGr`, with kernel control (`LT x = 0` pushes one step deeper)
and lift-back surjectivity. Residual (construction goes through
`filtr_extend_of_iotaMulti`: define on `c • ιMulti` generators, extend by
linearity). Stated with plain functions + equations (no bundled homs, no
subtype arithmetic) so all uses are syntactic. -/
def FiltrLeadData
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P)) :
    Prop :=
  ∃ LT : ∀ (_t k : ℕ), ↥(⋀[FRL P]^k (Fin d → FRL P)) →
      ↥(⋀[grRegular P]^k (Fin d → grRegular P)),
    (∀ (t k : ℕ), LT t k 0 = 0) ∧
    (∀ (t k : ℕ) (x y : ↥(⋀[FRL P]^k (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t k) (_hy : y ∈ filtrPiece P d t k),
      LT t k (x + y) = LT t k x + LT t k y) ∧
    (∀ (t k : ℕ) (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t (k + 1))
      (_hdx : koszulContract (koszulContractOfSequence g) k x ∈
        filtrPiece P d t k),
      LT t k (koszulContract (koszulContractOfSequence g) k x) =
        koszulContract (grlift_phiGr P d g hgen) k (LT t (k + 1) x)) ∧
    (∀ (t k : ℕ) (x : ↥(⋀[FRL P]^(k + 1) (Fin d → FRL P)))
      (_hx : x ∈ filtrPiece P d t (k + 1)),
      LT t (k + 1) x = 0 → x ∈ filtrPiece P d (t + 1) (k + 1)) ∧
    ∀ (t k : ℕ) (W : ↥(⋀[grRegular P]^((k + 1) + 1) (Fin d → grRegular P))),
      ∃ x : ↥(⋀[FRL P]^((k + 1) + 1) (Fin d → FRL P)),
        x ∈ filtrPiece P d t ((k + 1) + 1) ∧ LT t ((k + 1) + 1) x = W

/-- Single-step lift: `z ∈ Z ∩ F(t)` is a boundary plus a strictly deeper
cycle. Proved from the data; conditional-exact on
`[FiltrGenBound, FiltrLeadData]` + gr-exactness. -/
theorem filtr_single_of_lead
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hGB : FiltrGenBound P d g) (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (t j : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d t (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d (t + 1) (j + 1) := by
  obtain ⟨LT, LT_zero, LT_add, hinter, hker, hsurj⟩ := hlead
  have hdx0 : koszulContract (koszulContractOfSequence g) j z ∈
      filtrPiece P d t j := by
    rw [hz]
    exact Submodule.zero_mem _
  have hLTcyc : koszulContract (grlift_phiGr P d g hgen) j
      (LT t (j + 1) z) = 0 := by
    have h := hinter t j z hzF hdx0
    rw [hz, LT_zero] at h
    exact h.symm
  obtain ⟨W, hW⟩ := hgr j _ hLTcyc
  obtain ⟨x, hx, hxW⟩ := hsurj t j W
  have hdwF : koszulContract (koszulContractOfSequence g) (j + 1) x ∈
      filtrPiece P d t (j + 1) := by
    have hle := filtr_d_preshift P d g hGB t (j + 1)
    apply hle
    exact Submodule.mem_map_of_mem hx
  refine ⟨x, z - koszulContract (koszulContractOfSequence g) (j + 1) x,
    ?_, ?_, ?_⟩
  · rw [add_sub_cancel]
  · rw [map_sub, hz]
    have h2 : koszulContract (koszulContractOfSequence g) j
        (koszulContract (koszulContractOfSequence g) (j + 1) x) = 0 := by
      have hcomp := congrArg (fun f => f x)
        (koszulContract_comp (koszulContractOfSequence g) j)
      simpa using hcomp
    rw [h2, sub_zero]
  · have hz'F : z - koszulContract (koszulContractOfSequence g) (j + 1) x ∈
        filtrPiece P d t (j + 1) :=
      Submodule.sub_mem _ hzF hdwF
    have hLTsub : LT t (j + 1)
          (z - koszulContract (koszulContractOfSequence g) (j + 1) x) =
        LT t (j + 1) z -
          LT t (j + 1) (koszulContract (koszulContractOfSequence g) (j + 1) x) := by
      have h1 := LT_add t (j + 1)
        (z - koszulContract (koszulContractOfSequence g) (j + 1) x)
        (koszulContract (koszulContractOfSequence g) (j + 1) x) hz'F hdwF
      rw [sub_add_cancel] at h1
      rw [h1, add_sub_cancel_right]
    have hinter_x2 : LT t (j + 1)
          (koszulContract (koszulContractOfSequence g) (j + 1) x) =
        LT t (j + 1) z :=
      (hinter t (j + 1) x hx hdwF).trans (by rw [hxW]; exact hW)
    have h0 : LT t (j + 1)
        (z - koszulContract (koszulContractOfSequence g) (j + 1) x) = 0 := by
      rw [hLTsub, hinter_x2, sub_self]
    exact hker t j _ hz'F h0

/-! ## §4. Iteration to the Artin–Rees index -/

/-- Iteration: every cycle is a boundary plus a cycle arbitrarily deep in
the filtration. Proved; conditional-exact on
`[FiltrGenBound, FiltrLeadData]` + gr-exactness. -/
theorem filtr_iterate
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hGB : FiltrGenBound P d g) (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (j N : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0) :
    ∃ W : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ zN : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) W + zN = z ∧
      koszulContract (koszulContractOfSequence g) j zN = 0 ∧
      zN ∈ filtrPiece P d N (j + 1) := by
  induction N with
  | zero =>
      refine ⟨0, z, ?_, hz, ?_⟩
      · rw [map_zero, zero_add]
      · rw [filtrPiece_eq_top_of_le P d 0 (j + 1) (Nat.zero_le _)]
        exact Submodule.mem_top
  | succ n ih =>
      obtain ⟨Wn, zn, hWn, hzn, hznF⟩ := ih
      obtain ⟨w, z', hw, hz', hz'F⟩ :=
        filtr_single_of_lead P d g hgen hGB hlead hgr n j zn hzn hznF
      refine ⟨Wn + w, z', ?_, hz', hz'F⟩
      rw [map_add]
      have hstep : koszulContract (koszulContractOfSequence g) (j + 1) Wn +
          koszulContract (koszulContractOfSequence g) (j + 1) w + z' =
          koszulContract (koszulContractOfSequence g) (j + 1) Wn + zn := by
        rw [add_assoc, hw]
      rw [hstep]
      exact hWn

set_option maxSynthPendingDepth 4 in
set_option maxHeartbeats 2000000 in
-- Resource knobs (see module docstring): depth 4 for quotient TC (as in
-- file 6); 2000000 heartbeats for the ~25-tactic homology chase (default
-- budget and 1000000 both verified insufficient).
/-- The homology consequence `𝔪 • H = H` from gr-exactness, via iteration
to one past the Artin–Rees index. Proved from the data;
conditional-exact on `[FiltrGenBound, FiltrLeadData]`. -/
theorem filtr_hconseq_of_lead
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hGB : FiltrGenBound P d g) (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j') (j : ℕ) :
    IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          (grlift_homology (koszulContractOfSequence g) j)) = ⊤ := by
  refine le_antisymm Submodule.smul_le_right ?_
  intro h _
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective
    (grlift_boundaries (koszulContractOfSequence g) j) h
  change (grlift_boundaries (koszulContractOfSequence g) j).mkQ q ∈
    IsLocalRing.maximalIdeal (FRL P) • (⊤ : Submodule (FRL P)
      (grlift_homology (koszulContractOfSequence g) j))
  obtain ⟨kAR, hkAR⟩ := filtr_ar_index P d g j
  have hexp : (j + 1) + kAR + 1 - (j + 1) = kAR + 1 := by omega
  have hz : koszulContract (koszulContractOfSequence g) j
      (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) = 0 :=
    LinearMap.mem_ker.mp q.2
  have hiter := filtr_iterate P d g hgen hGB hlead hgr j ((j + 1) + kAR + 1)
    (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) hz
  obtain ⟨W, zN, hW, hzN, hzNF⟩ := hiter
  have hzNmem : zN ∈ IsLocalRing.maximalIdeal (FRL P) ^ (kAR + 1) • ⊤ ⊓
      grlift_cycles (koszulContractOfSequence g) j := by
    constructor
    · rw [filtrPiece_def, hexp] at hzNF
      exact hzNF
    · exact LinearMap.mem_ker.mpr hzN
  rw [hkAR (kAR + 1) (Nat.le_succ _)] at hzNmem
  have hsub : kAR + 1 - kAR = 1 := by omega
  rw [hsub, pow_one] at hzNmem
  have hzNZ : zN ∈ IsLocalRing.maximalIdeal (FRL P) •
      grlift_cycles (koszulContractOfSequence g) j :=
    Submodule.smul_mono le_rfl inf_le_right hzNmem
  have hmap : Submodule.map (grlift_cycles (koszulContractOfSequence g) j).subtype
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) =
        IsLocalRing.maximalIdeal (FRL P) •
          grlift_cycles (koszulContractOfSequence g) j := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hzNZ' : (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
      ↥(grlift_cycles (koszulContractOfSequence g) j)) ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          ↥(grlift_cycles (koszulContractOfSequence g) j)) := by
    have hmem : zN ∈ Submodule.map
        (grlift_cycles (koszulContractOfSequence g) j).subtype
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) := by
      rw [hmap]
      exact hzNZ
    obtain ⟨w, hw, hwx⟩ := hmem
    have heq : w = ⟨zN, LinearMap.mem_ker.mpr hzN⟩ := Subtype.ext hwx
    rwa [heq] at hw
  have hle : Submodule.map
        (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            ↥(grlift_cycles (koszulContractOfSequence g) j))) ≤
        IsLocalRing.maximalIdeal (FRL P) •
          (⊤ : Submodule (FRL P)
            (grlift_homology (koszulContractOfSequence g) j)) :=
    Submodule.map_le_iff_le_comap.mpr
      (Submodule.smul_top_le_comap_smul_top _ _)
  have hfin : (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          (grlift_homology (koszulContractOfSequence g) j)) :=
    hle (Submodule.mem_map_of_mem hzNZ')
  have hdW : koszulContract (koszulContractOfSequence g) j
      (koszulContract (koszulContractOfSequence g) (j + 1) W) = 0 := by
    have hcomp := congrArg (fun f => f W)
      (koszulContract_comp (koszulContractOfSequence g) j)
    simpa using hcomp
  have hqeq : (grlift_boundaries (koszulContractOfSequence g) j).mkQ q =
      (grlift_boundaries (koszulContractOfSequence g) j).mkQ
        (⟨zN, LinearMap.mem_ker.mpr hzN⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) := by
    have hsplit : q =
        (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
          ↥(grlift_cycles (koszulContractOfSequence g) j)) +
        ⟨zN, LinearMap.mem_ker.mpr hzN⟩ := by
      apply Subtype.ext
      change (q : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P))) =
        koszulContract (koszulContractOfSequence g) (j + 1) W + zN
      exact hW.symm
    rw [hsplit, map_add]
    have hbdry : (grlift_boundaries (koszulContractOfSequence g) j).mkQ
          (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
            ↥(grlift_cycles (koszulContractOfSequence g) j)) = 0 := by
      change Submodule.Quotient.mk
          (⟨koszulContract (koszulContractOfSequence g) (j + 1) W,
            LinearMap.mem_ker.mpr hdW⟩ :
            ↥(grlift_cycles (koszulContractOfSequence g) j)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      rw [Submodule.mem_comap]
      exact ⟨W, rfl⟩
    simp only [hbdry, zero_add]
  rw [hqeq]
  exact hfin

set_option maxSynthPendingDepth 4 in
/-- File-6 residual discharged modulo the two handoffs:
`GrLiftFiltrationConseq` from `[FiltrGenBound, FiltrLeadData]`.
conditional-exact. -/
theorem filtr_grlift_conseq_of_lead
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hGB : FiltrGenBound P d g) (hlead : FiltrLeadData P d g hgen) :
    GrLiftFiltrationConseq P d g hgen := by
  intro hgr j
  exact filtr_hconseq_of_lead P d g hgen hGB hlead hgr j

#print axioms filtr_ar_index
#print axioms filtr_phi_mem
#print axioms filtr_d_preshift
#print axioms filtr_extend_of_iotaMulti
#print axioms filtr_single_of_lead
#print axioms filtr_iterate
#print axioms filtr_hconseq_of_lead
#print axioms filtr_grlift_conseq_of_lead

/-! ## §5. The generator bound from the contraction formula -/

/-- The generator bound holds whenever the sequence spans `𝔪`: feed L3's
alternating-sum formula `koszulContract_ιMulti`, whose coefficients
`(-1)^j * φ (v j)` lie in `𝔪` by `filtr_phi_mem`, then close each
summand by `Submodule.smul_mem_smul`. Discharges the `FiltrGenBound`
residual modulo the genuine hypothesis `hgen` (which is necessary:
without it the bound is false — e.g. `g = 1` gives a contraction of
`1 ∉ 𝔪 • ⊤`).
-/
theorem filtr_genBound_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P)) :
    FiltrGenBound P d g := by
  intro k v
  change koszulContract (koszulContractOfSequence g) k
      ⟨ExteriorAlgebra.ιMulti (FRL P) (Nat.succ k) v,
        mem_ιMulti_piece (Nat.succ k) v⟩ ∈
      IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P) ↥(⋀[FRL P]^k (Fin d → FRL P)))
  rw [EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ContractionFormula.koszulContract_ιMulti]
  refine sum_mem fun j _ => ?_
  have hφ : koszulContractOfSequence g (v j) ∈ IsLocalRing.maximalIdeal (FRL P) :=
    filtr_phi_mem P d g hgen (v j)
  have hc : (-1 : FRL P) ^ j.val * koszulContractOfSequence g (v j) ∈
      IsLocalRing.maximalIdeal (FRL P) :=
    (IsLocalRing.maximalIdeal (FRL P)).mul_mem_left _ hφ
  exact Submodule.smul_mem_smul hc Submodule.mem_top

/-- Shifted preservation from the spanning hypothesis alone: `FiltrGenBound`
discharged at the §2 level. Unconditional modulo `hgen` (no residuals). -/
theorem filtr_d_preshift_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (t j : ℕ) :
    Submodule.map (koszulContract (koszulContractOfSequence g) j)
        (filtrPiece P d t (j + 1)) ≤ filtrPiece P d t j :=
  filtr_d_preshift P d g (filtr_genBound_of_span P d g hgen) t j

/-- Single-step lift with `FiltrGenBound` discharged. Conditional-exact on
`[FiltrLeadData]` + gr-exactness. -/
theorem filtr_single_of_lead_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (t j : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0)
    (hzF : z ∈ filtrPiece P d t (j + 1)) :
    ∃ w : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ z' : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) w + z' = z ∧
      koszulContract (koszulContractOfSequence g) j z' = 0 ∧
      z' ∈ filtrPiece P d (t + 1) (j + 1) :=
  filtr_single_of_lead P d g hgen (filtr_genBound_of_span P d g hgen)
    hlead hgr t j z hz hzF

/-- Iteration with `FiltrGenBound` discharged. Conditional-exact on
`[FiltrLeadData]` + gr-exactness. -/
theorem filtr_iterate_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j')
    (j N : ℕ) (z : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)))
    (hz : koszulContract (koszulContractOfSequence g) j z = 0) :
    ∃ W : ↥(⋀[FRL P]^((j + 1) + 1) (Fin d → FRL P)),
    ∃ zN : ↥(⋀[FRL P]^(j + 1) (Fin d → FRL P)),
      koszulContract (koszulContractOfSequence g) (j + 1) W + zN = z ∧
      koszulContract (koszulContractOfSequence g) j zN = 0 ∧
      zN ∈ filtrPiece P d N (j + 1) :=
  filtr_iterate P d g hgen (filtr_genBound_of_span P d g hgen)
    hlead hgr j N z hz

/-- The homology consequence with `FiltrGenBound` discharged.
conditional-exact on `[FiltrLeadData]` + gr-exactness. -/
theorem filtr_hconseq_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadData P d g hgen)
    (hgr : ∀ j', contractExactAt (grlift_phiGr P d g hgen) j') (j : ℕ) :
    IsLocalRing.maximalIdeal (FRL P) •
        (⊤ : Submodule (FRL P)
          (grlift_homology (koszulContractOfSequence g) j)) = ⊤ :=
  filtr_hconseq_of_lead P d g hgen (filtr_genBound_of_span P d g hgen)
    hlead hgr j

/-- File-6 residual discharged modulo the leading-term data alone:
`GrLiftFiltrationConseq` from `[FiltrLeadData]`. Conditional-exact. -/
theorem filtr_grlift_conseq_of_span
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (FRL P))
    (hlead : FiltrLeadData P d g hgen) :
    GrLiftFiltrationConseq P d g hgen :=
  filtr_grlift_conseq_of_lead P d g hgen
    (filtr_genBound_of_span P d g hgen) hlead

#print axioms filtr_genBound_of_span
#print axioms filtr_d_preshift_of_span
#print axioms filtr_single_of_lead_of_span
#print axioms filtr_iterate_of_span
#print axioms filtr_hconseq_of_span
#print axioms filtr_grlift_conseq_of_span

end FiltrationLift
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
