/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParameters
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.PolynomialExactness
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The gr-lift: sop, gr-exactness, and R2 (A4(iii), file 6 of 6)

Foundation + missing-2 + the gr-exact-implies-exact lift for the Koszul
exactness route (R2: `K(sop)` exact over `R_P`). Design: ker/range chase,
not LES/`δ` (the `δ`-as-`×x` identification is absent from Mathlib).

* (§1) The sop: the SystemOfParameters minimal-cardinality spanning family as a
  `Fin`-family, with `d = spanFinrank 𝔪` (spanning), `d = dim 𝔪/𝔪²`
  (cotangent finrank, i.e. Nakayama packaged in Mathlib), R-2b′ minimality,
  and the dimension equation. All unconditional.
* (§2) missing-2: file-5 `koszul_poly_augmented_exact` transported along the
  M4c gr-equivalence to gr-side exactness. The transfer lemmas
  (`grlift_exact_transfer`, `grlift_aug_transfer`, `grlift_surj_transfer`)
  are proved; the exterior-power/ring-change bridge is the explicit residual
  `GrLiftIntertwining`. `ker = ⊥` is taken as hypothesis `hker` in the exact
  M4c-ii shape and is not proved here; the `X ↦ gr-class` computation for
  the `ker`-built equiv is proved (`grlift_grEquiv_comp`).
* (§3) The lift: gr-exactness forces `K(sop)` exact over `R_P` via Nakayama
  on homology. The schema (`grlift_exact_of_grConsequence`, with exterior
  finiteness + Nakayama vanishing proved) turns the filtration consequence
  `𝔪 • H = H` into exactness; the filtration half is the explicit residual
  `GrLiftFiltrationConseq`. Masters `grlift_r2_exact_of_equiv` /
  `grlift_r2_exact` / `grlift_master` are conditional-exact on
  `[hker⊥/hgrEquiv, GrLiftIntertwining, GrLiftFiltrationConseq]`.

## References

Project (all read-only): `Regularity/Koszul/SystemOfParameters.lean` (sop extraction),
`Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`mult_ringKrullDim_atPrime_eq_of_minimal`),
`Regularity/Koszul/PolynomialExactness.lean` (file 5: `koszul_poly_augmented_exact`),
`Regularity/Koszul/AugmentedConeStep.lean` (file 4: `contractExactAt`,
`contractAugExactZero`), `Regularity/Koszul/KoszulComplex.lean` (`koszulContract`,
`koszulContractOfSequence`), `Regularity/Koszul/GradedSurjection.lean` (`genClass`,
`polySurj_X`, `polySurjResidue`, `polySurjResidue_quotKerEquiv`),
`Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece`, `grRegular`),
`Regularity/Koszul/FiltrationStability.lean` (`maximalIdeal_atPrime_ne_top`).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/Module/SpanRankOperations.lean`:
  `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`.
* `RingTheory/Ideal/Cotangent.lean`: `IsLocalRing.CotangentSpace`.
* `RingTheory/LocalRing/ResidueField/Defs.lean`: `ResidueField`, its field
  instance.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean`: `mem_maximalIdeal`.
* `RingTheory/Finiteness/Nakayama.lean`:
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`.
* `RingTheory/Finiteness/Defs.lean`: `Submodule.fg_def`, `Module.finite_def`.
* `RingTheory/Finiteness/Basic.lean`: `Module.Finite.pi`,
  `Module.Finite.quotient`, `Module.Finite.iff_fg`, `Module.Finite.fg_top`.
* `RingTheory/Noetherian/Basic.lean`:
  `isNoetherian_of_isNoetherianRing_of_finite`, `IsNoetherian.noetherian`.
* `LinearAlgebra/ExteriorPower/Basic.lean`: `exteriorPower.zeroEquiv`,
  `exteriorPower.ιMulti_span_of_span`.
* `RingTheory/Ideal/Quotient/Operations.lean`:
  `RingHom.quotientKerEquivOfSurjective_apply_mk`,
  `RingEquiv.quotientBot_symm_mk`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `Ideal.quotEquivOfEq_mk`.
* `Data/Fintype/EquivFin.lean`: `Finset.equivFin`.

## Status

* §1 (sop + R-2b′ + dim equation): unconditional.
* §2 transfer lemmas + `X ↦ gr-class` computation: unconditional.
  `grlift_grExact_of_intertwining`: conditional-exact on
  `[hgrEquiv, GrLiftIntertwining]`.
* §3 schema (finiteness + Nakayama vanishing + lift): unconditional.
  `grlift_r2_exact*`: conditional-exact on
  `[hker⊥/hgrEquiv, GrLiftIntertwining, GrLiftFiltrationConseq]`.
* Residuals (explicit, unproved): `GrLiftIntertwining` (missing-2 bridge),
  `GrLiftFiltrationConseq` (filtration half of the lift).

## Resource knobs (inventoried, permitted class)

`set_option maxSynthPendingDepth 4 in` (scoped, minimal bump over the repo
default 3) on `grlift_homology`, `GrLiftFiltrationConseq`,
`grlift_exact_of_grConsequence`, `grlift_r2_exact_of_equiv`,
`grlift_r2_exact`, `grlift_master`: the nested TC for submodule quotients
over a `ker`-of-`koszulContract` ambient exceeds depth 3 (verified: depth 4
suffices, and the same goals elaborate standalone). Not a linter
suppression: without it the declarations do not elaborate at all.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedLift

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SystemOfParameters
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PolynomialExactness
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The residue field of `R_P` (reducible, so the field instance flows). -/
abbrev grliftK : Type _ := IsLocalRing.ResidueField (Localization.AtPrime P)

/-! ## §1. The sop: minimal spanning family, R-2b′ closed -/

/-- A spanning finset as a `Fin`-family (the `polySurj`/`K(sop)` input shape). -/
noncomputable def grlift_family {R : Type*} (s : Finset R) : Fin s.card → R :=
  fun i => ↑(s.equivFin.symm i)

/-- The family hits exactly the finset. -/
theorem grlift_family_range {R : Type*} (s : Finset R) :
    Set.range (grlift_family s) = ↑s := by
  ext x
  simp only [grlift_family, Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩,
      congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, hx⟩)⟩

/-- The sop exists with `d = spanFinrank 𝔪` (SystemOfParameters, read-only). -/
theorem grlift_sop_exists :
    ∃ d : ℕ, ∃ g : Fin d → Localization.AtPrime P,
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  obtain ⟨s, hspan, hcard, _hdim⟩ := exists_finset_span_maximalIdeal_atPrime P
  refine ⟨s.card, grlift_family s, ?_, hcard⟩
  rw [grlift_family_range]
  exact hspan

/-- `d = dim 𝔪/𝔪²`: minimal #gens equals the cotangent-space finrank.
This is Nakayama's lemma, packaged in Mathlib. Shape binders `g`/`hgen`
record the sop context. -/
theorem grlift_sop_cotangent_dim (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (_hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank) :
    d = Module.finrank (grliftK P)
      (IsLocalRing.CotangentSpace (Localization.AtPrime P)) := by
  rw [hd]
  exact IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace _

/-- R-2b′ closed: the sop is minimal (`d ≤ min #gens`). -/
theorem grlift_sop_minimal (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (_hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank) :
    d ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  rw [hd]

/-- The dimension equation from minimality (Multiplicity, read-only). -/
theorem grlift_dim_eq_of_sop (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank) :
    ringKrullDim (Localization.AtPrime P) = d :=
  mult_ringKrullDim_atPrime_eq_of_minimal P d g hgen
    (grlift_sop_minimal P d g hgen hd)

/-- Bundle: the file-6 sop with spanning, minimality, cotangent dimension,
and the dimension equation. -/
theorem grlift_sop_full :
    ∃ d : ℕ, ∃ g : Fin d → Localization.AtPrime P,
      Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ∧
      d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank ∧
      d = Module.finrank (grliftK P)
        (IsLocalRing.CotangentSpace (Localization.AtPrime P)) ∧
      ringKrullDim (Localization.AtPrime P) = d := by
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists P
  exact ⟨d, g, hgen, hd, grlift_sop_cotangent_dim P d g hgen hd,
    grlift_dim_eq_of_sop P d g hgen hd⟩

/-! ## §2. Missing-2: gr-exactness over `gr ≅ κ[t]` -/

/-- The gr-side generator classes: images of the sop in `gr¹`, as elements
of `gr` (the `polySurj_X` values). -/
noncomputable def grlift_grClass (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) (i : Fin d) :
    grRegular P :=
  DirectSum.of (grPiece (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 1
    (genClass (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g i hgen)

/-- The gr-side Koszul functional: contraction against the gr-generator
sequence. -/
noncomputable def grlift_phiGr (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (Fin d → grRegular P) →ₗ[grRegular P] grRegular P :=
  koszulContractOfSequence (fun i => grlift_grClass P d g hgen i)

/-- Exactness transfers along intertwining bijections. Proved (pure
transport of the file-4 `∀∃` predicates). Plain `Equiv`s suffice: the
transfer uses only commutation with the differentials plus `0 ↦ 0`
(`hE0`); no semilinearity is needed (this also avoids the cross-ring
`Module` structures a `≃ₛₗ` would demand). -/
theorem grlift_exact_transfer {S T : Type*} [CommRing S] [CommRing T]
    {N : Type*} [AddCommGroup N] [Module S N]
    {N' : Type*} [AddCommGroup N'] [Module T N']
    (ψ : N →ₗ[S] S) (φ : N' →ₗ[T] T)
    (E : ∀ k : ℕ, ↥(⋀[S]^k N) ≃ ↥(⋀[T]^k N'))
    (hE0 : ∀ k : ℕ, E k 0 = 0)
    (hcomm : ∀ k : ℕ, ∀ w : ↥(⋀[S]^(k + 1) N),
      E k (koszulContract ψ k w) =
        koszulContract φ k (E (k + 1) w))
    (j : ℕ) (hexact : contractExactAt ψ j) :
    contractExactAt φ j := by
  intro z hz
  have h1 := hcomm j ((E (j + 1)).symm z)
  rw [Equiv.apply_symm_apply, hz] at h1
  have hsymm : koszulContract ψ j ((E (j + 1)).symm z) = 0 :=
    (E j).injective (by simp [h1, hE0 j])
  obtain ⟨w, hw⟩ := hexact _ hsymm
  exact ⟨E ((j + 1) + 1) w, by rw [← hcomm, hw, Equiv.apply_symm_apply]⟩

/-- Augmentation transfers along intertwining data (`τ` = target map).
proved. -/
theorem grlift_aug_transfer {S T : Type*} [CommRing S] [CommRing T]
    {N : Type*} [AddCommGroup N] [Module S N]
    {N' : Type*} [AddCommGroup N'] [Module T N']
    {QS : Type*} [AddCommGroup QS] [Module S QS]
    {QT : Type*} [AddCommGroup QT] [Module T QT]
    (σ' : S →+* T)
    (ψ : N →ₗ[S] S) (φ : N' →ₗ[T] T)
    (E0 : ↥(⋀[S]^0 N) ≃ ↥(⋀[T]^0 N'))
    (E1 : ↥(⋀[S]^1 N) ≃ ↥(⋀[T]^1 N'))
    (hcomm0 : ∀ a : ↥(⋀[S]^1 N),
      E0 (koszulContract ψ 0 a) = koszulContract φ 0 (E1 a))
    (εS : ↥(⋀[S]^0 N) →ₗ[S] QS) (εT : ↥(⋀[T]^0 N') →ₗ[T] QT)
    (τ : QS →ₛₗ[σ'] QT)
    (hτ : ∀ b : ↥(⋀[S]^0 N), τ (εS b) = εT (E0 b))
    (hτinj : Function.Injective τ)
    (haug : contractAugExactZero ψ εS) :
    contractAugExactZero φ εT := by
  constructor
  · intro a
    have ha : a = E1 ((E1).symm a) := (Equiv.apply_symm_apply _ _).symm
    rw [ha, ← hcomm0, ← hτ, haug.1, map_zero]
  · intro c hc
    have h0 : εS ((E0).symm c) = 0 :=
      hτinj (by rw [hτ, Equiv.apply_symm_apply, hc, map_zero])
    obtain ⟨c', hc'⟩ := haug.2 _ h0
    exact ⟨E1 c', by rw [← hcomm0, hc', Equiv.apply_symm_apply]⟩

/-- Surjectivity transfers along a surjective target map. Proved. -/
theorem grlift_surj_transfer {S T : Type*} [CommRing S] [CommRing T]
    {N : Type*} [AddCommGroup N] [Module S N]
    {N' : Type*} [AddCommGroup N'] [Module T N']
    {QS : Type*} [AddCommGroup QS] [Module S QS]
    {QT : Type*} [AddCommGroup QT] [Module T QT]
    (σ' : S →+* T)
    (E0 : ↥(⋀[S]^0 N) ≃ ↥(⋀[T]^0 N'))
    (εS : ↥(⋀[S]^0 N) →ₗ[S] QS) (εT : ↥(⋀[T]^0 N') →ₗ[T] QT)
    (τ : QS →ₛₗ[σ'] QT)
    (hτ : ∀ b : ↥(⋀[S]^0 N), τ (εS b) = εT (E0 b))
    (hsurj : Function.Surjective εS) (hτsurj : Function.Surjective τ) :
    Function.Surjective εT := by
  intro q
  obtain ⟨q', hq'⟩ := hτsurj q
  obtain ⟨b, hb⟩ := hsurj q'
  exact ⟨E0 b, by rw [← hτ, hb, hq']⟩

/-- Missing-2 residual: intertwining data between file-5's tower and the
gr-side (degree-wise exterior bijections commuting with the differentials,
plus the gr-side augmentation and an injective/surjective target map).
residual (the exterior-power/ring-change bridge, absent from Mathlib).
The augmentation is carried as residual data (rather than constructed via
`Submodule.mkQ`, whose `Module`-TC over `grRegular` does not close in this
Mathlib version); the `X ↦ gr-class` computation (`grlift_grEquiv_comp`) is
proved separately and records why this residual is expected to close for
the M4c-ii equiv. -/
def GrLiftIntertwining (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hgrEquiv : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P) : Prop :=
  ∃ E : ∀ k : ℕ,
      ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^k (towerMod (grliftK P) d d)) ≃
        ↥(⋀[grRegular P]^k (Fin d → grRegular P)),
    (∀ k : ℕ, E k 0 = 0) ∧
    (∀ k : ℕ, ∀ w :
        ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^(k + 1)
          (towerMod (grliftK P) d d)),
      E k (koszulContract (towerPhi (grliftK P) d d) k w) =
        koszulContract (grlift_phiGr P d g hgen) k (E (k + 1) w)) ∧
    ∃ εgr : ↥(⋀[grRegular P]^0 (Fin d → grRegular P)) →ₗ[grRegular P]
        (grRegular P ⧸ Ideal.span
          (Set.range (fun i => grlift_grClass P d g hgen i))),
      ∃ τ : (MvPolynomial (Fin d) (grliftK P) ⧸ towerIdeal (grliftK P) d d)
          →ₛₗ[hgrEquiv.toRingHom]
          (grRegular P ⧸ Ideal.span
            (Set.range (fun i => grlift_grClass P d g hgen i))),
        (∀ b : ↥(⋀[MvPolynomial (Fin d) (grliftK P)]^0
            (towerMod (grliftK P) d d)),
          τ (towerAug (grliftK P) d d (le_refl d) b) = εgr (E 0 b)) ∧
        Function.Injective τ ∧ Function.Surjective τ

/-- Missing-2 master: file-5 exactness transported to the gr-side.
conditional-exact on `[hgrEquiv, GrLiftIntertwining]` + proved inputs. -/
theorem grlift_grExact_of_intertwining (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hgrEquiv : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hint : GrLiftIntertwining P d g hgen hgrEquiv) :
    (∀ j, contractExactAt (grlift_phiGr P d g hgen) j) ∧
      ∃ εgr : ↥(⋀[grRegular P]^0 (Fin d → grRegular P)) →ₗ[grRegular P]
        (grRegular P ⧸ Ideal.span
          (Set.range (fun i => grlift_grClass P d g hgen i))),
        contractAugExactZero (grlift_phiGr P d g hgen) εgr ∧
          Function.Surjective εgr := by
  obtain ⟨hexact5, haug5, hsurj5⟩ := koszul_poly_augmented_exact (grliftK P) d
  obtain ⟨E, hE0, hcomm, εgr, τ, hτ, hτinj, hτsurj⟩ := hint
  refine ⟨?_, εgr, ?_, ?_⟩
  · intro j
    exact grlift_exact_transfer _ _ E hE0 hcomm j (hexact5 j)
  · exact grlift_aug_transfer hgrEquiv.toRingHom _ _ (E 0) (E 1) (hcomm 0) _ _
      τ hτ hτinj haug5
  · exact grlift_surj_transfer hgrEquiv.toRingHom (E 0) _ _ τ hτ hsurj5
      hτsurj

/-- The gr-equivalence built from `ker = ⊥`: first-isomorphism collapse
along `quotientBot` (same construction as `hsAssemble_isoOfKerEqBot`, in
transparent form so the `X` computation below closes by `rfl`-lemmas). -/
noncomputable def grlift_grEquivOfKerEqBot (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P :=
  (RingEquiv.quotientBot _).symm.trans
    ((Ideal.quotEquivOfEq hker.symm).trans
      (polySurjResidue_quotKerEquiv P d g hgen))

/-- The `ker`-built equiv sends `Xᵢ` to the gr-class of `gᵢ`. Proved (the
value computation the intertwining residual is expected to lie over). -/
theorem grlift_grEquiv_comp (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) (i : Fin d) :
    grlift_grEquivOfKerEqBot P d g hgen hker (MvPolynomial.X i) =
      grlift_grClass P d g hgen i := by
  have h1 : (RingEquiv.quotientBot
      (MvPolynomial (Fin d) (grliftK P))).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk ⊥ (MvPolynomial.X i) := rfl
  simp only [grlift_grEquivOfKerEqBot, polySurjResidue_quotKerEquiv,
    RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  change polySurjResidue P d g hgen (MvPolynomial.X i) = _
  change polySurj (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) d g hgen
    (MvPolynomial.X i) = _
  rw [polySurj_X]
  rfl

/-! ## §3. The lift: gr-exact ⇒ exact over `R_P` -/

/-- Cycles at degree `j + 1`. `abbrev` so membership lemmas match. -/
abbrev grlift_cycles {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] R) (j : ℕ) : Submodule R ↥(⋀[R]^(j + 1) M) :=
  LinearMap.ker (koszulContract φ j)

/-- Boundaries at degree `j + 1`, as a submodule of cycles. `abbrev` so
membership lemmas match. -/
abbrev grlift_boundaries {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (j : ℕ) :
    Submodule R ↥(grlift_cycles φ j) :=
  (LinearMap.range (koszulContract φ (j + 1))).comap
    (grlift_cycles φ j).subtype

set_option maxSynthPendingDepth 4 in
-- Minimal bump over the repo default 3 (resource knob): the nested TC for
-- this quotient over a `ker`-of-`koszulContract` ambient exceeds depth 3.
/-- The Koszul homology at degree `j + 1` (cycles mod boundaries).
`abbrev` (like `grPiece`) so downstream instances see through it. -/
abbrev grlift_homology {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (j : ℕ) : Type _ :=
  ↥(grlift_cycles φ j) ⧸ grlift_boundaries φ j

/-- Exterior powers of `Fin d → R_P` are finite (wedges of a finite spanning
set span, via `ιMulti_span_of_span`). -/
instance grlift_exterior_finite (d k : ℕ) :
    Module.Finite (Localization.AtPrime P)
      ↥(⋀[Localization.AtPrime P]^k (Fin d → Localization.AtPrime P)) := by
  obtain ⟨t, htfin, hspan⟩ := Submodule.fg_def.mp
    (Module.Finite.fg_top (R := Localization.AtPrime P)
      (M := Fin d → Localization.AtPrime P))
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨exteriorPower.ιMulti _ _ ''
    {a : Fin k → (Fin d → Localization.AtPrime P) |
      Set.range a ⊆ t}, ?_, ?_⟩
  · have hdom : {a : Fin k → (Fin d → Localization.AtPrime P) |
        Set.range a ⊆ t}.Finite := by
      let e : {a : Fin k → (Fin d → Localization.AtPrime P) //
          Set.range a ⊆ t} ≃ ((i : Fin k) → ↥t) :=
        { toFun := fun a i => ⟨a.1 i, Set.range_subset_iff.mp a.2 i⟩,
          invFun := fun f => ⟨fun i => ((f i : ↥t) :
            Fin d → Localization.AtPrime P), fun y hy => by
            obtain ⟨i, rfl⟩ := hy
            exact (f i).2⟩,
          left_inv := fun a => Subtype.ext (funext fun _ => rfl),
          right_inv := fun f => by ext i; rfl }
      have : Fintype ↥t := htfin.fintype
      have : Fintype ↥{a : Fin k → (Fin d → Localization.AtPrime P) |
          Set.range a ⊆ t} := Fintype.ofEquiv _ e.symm
      exact Set.toFinite _
    exact hdom.image _
  · exact exteriorPower.ιMulti_span_of_span _ _ _ hspan

/-- Nakayama vanishing for Koszul homology: `𝔪 • H = H` forces `H = ⊥`.
proved (Mathlib Nakayama + units outside `𝔪`). -/
theorem grlift_quotient_eq_bot_of_smul_eq_top
    {H : Type*} [AddCommGroup H] [Module (Localization.AtPrime P) H]
    [Module.Finite (Localization.AtPrime P) H]
    (hH : IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P) H) = ⊤) :
    (⊤ : Submodule (Localization.AtPrime P) H) = ⊥ := by
  have hFG : (⊤ : Submodule (Localization.AtPrime P) H).FG :=
    Module.Finite.fg_top
  obtain ⟨r, hr, hrkill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ⊤ hFG
      (le_of_eq hH.symm)
  have hrU : IsUnit r := by
    by_contra hcon
    have hmem : r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon)
    have h1 : (1 : Localization.AtPrime P) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      have hsub :=
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).sub_mem hmem hr
      rwa [sub_sub_cancel] at hsub
    exact maximalIdeal_atPrime_ne_top P
      ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).eq_top_of_isUnit_mem
        h1 isUnit_one)
  obtain ⟨u, rfl⟩ := hrU
  apply eq_bot_iff.mpr
  intro h _
  have h0 : ((u : (Localization.AtPrime P)ˣ) :
      Localization.AtPrime P) • h = 0 :=
    hrkill h Submodule.mem_top
  have hmul : ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
      Localization.AtPrime P)) * (u : Localization.AtPrime P)) = 1 := by
    simp
  calc h = (((((u⁻¹ : (Localization.AtPrime P)ˣ) :
        Localization.AtPrime P)) * (u : Localization.AtPrime P))) • h := by
          simp [hmul]
    _ = ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
        Localization.AtPrime P))) •
        ((u : Localization.AtPrime P) • h) := by rw [mul_smul]
    _ = ((((u⁻¹ : (Localization.AtPrime P)ˣ) :
        Localization.AtPrime P))) • 0 := by rw [h0]
    _ = 0 := by simp

set_option maxSynthPendingDepth 4 in
-- Same resource knob (consumes `grlift_homology` quotient instances).
/-- The lift schema: `𝔪 • H = H` at every degree forces `K(sop)` exact over
`R_P`. Proved (Nakayama on homology; cycles are FG since `R_P` is
Noetherian and exterior powers are finite). -/
theorem grlift_exact_of_grConsequence (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgrConseq : ∀ j : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P)
        (grlift_homology (koszulContractOfSequence g) j)) = ⊤)
    (j : ℕ) : contractExactAt (koszulContractOfSequence g) j := by
  have hC : (grlift_cycles (koszulContractOfSequence g) j).FG :=
    IsNoetherian.noetherian _
  have : Module.Finite (Localization.AtPrime P)
      ↥(grlift_cycles (koszulContractOfSequence g) j) :=
    Module.Finite.iff_fg.mpr hC
  have hbot : (⊤ : Submodule (Localization.AtPrime P)
      (grlift_homology (koszulContractOfSequence g) j)) = ⊥ :=
    grlift_quotient_eq_bot_of_smul_eq_top P (hgrConseq j)
  intro z hz
  have hmem : (Submodule.Quotient.mk (⟨z, hz⟩ :
      ↥(grlift_cycles (koszulContractOfSequence g) j)) :
      grlift_homology (koszulContractOfSequence g) j) ∈
      (⊤ : Submodule (Localization.AtPrime P)
        (grlift_homology (koszulContractOfSequence g) j)) :=
    Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  rw [Submodule.Quotient.mk_eq_zero] at hmem
  rw [Submodule.mem_comap] at hmem
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw⟩

set_option maxSynthPendingDepth 4 in
-- Same resource knob (consumes `grlift_homology` quotient instances).
/-- The filtration half: missing-2 gr-exactness forces `𝔪 • H = H` at every
degree. Residual (the filtration/nilpotency chase on `K(sop)`; needs the
`𝔪`-adic filtration of the Koszul complex + Artin–Rees comparison, absent
from Mathlib). -/
def GrLiftFiltrationConseq (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  (∀ j, contractExactAt (grlift_phiGr P d g hgen) j) →
    ∀ j, IsLocalRing.maximalIdeal (Localization.AtPrime P) •
      (⊤ : Submodule (Localization.AtPrime P)
        (grlift_homology (koszulContractOfSequence g) j)) = ⊤

set_option maxSynthPendingDepth 4 in
-- Same resource knob (consumes `grlift_homology` quotient instances).
/-- R2 master over an explicit gr-equivalence: `K(sop)` exact over `R_P`.
conditional-exact on
`[hgrEquiv, GrLiftIntertwining, GrLiftFiltrationConseq]`. -/
theorem grlift_r2_exact_of_equiv (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hgrEquiv : MvPolynomial (Fin d) (grliftK P) ≃+* grRegular P)
    (hint : GrLiftIntertwining P d g hgen hgrEquiv)
    (hfiltr : GrLiftFiltrationConseq P d g hgen) :
    ∀ j, contractExactAt (koszulContractOfSequence g) j := by
  have hgr := (grlift_grExact_of_intertwining P d g hgen hgrEquiv hint).1
  exact fun j => grlift_exact_of_grConsequence P d g (hfiltr hgr) j

set_option maxSynthPendingDepth 4 in
-- Same resource knob (consumes `grlift_homology` quotient instances).
/-- R2 master over `ker = ⊥`: `K(sop)` exact over `R_P`.
conditional-exact on `[hker⊥, GrLiftIntertwining, GrLiftFiltrationConseq]`
+ already-proved inputs. `hker⊥` is in the exact M4c-ii discharge shape
(`RingHom.ker (polySurjResidue P d g hgen) = ⊥`); it is not proved here. -/
theorem grlift_r2_exact (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (hint : GrLiftIntertwining P d g hgen
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    (hfiltr : GrLiftFiltrationConseq P d g hgen) :
    ∀ j, contractExactAt (koszulContractOfSequence g) j :=
  grlift_r2_exact_of_equiv P d g hgen
    (grlift_grEquivOfKerEqBot P d g hgen hker) hint hfiltr

set_option maxSynthPendingDepth 4 in
-- Same resource knob (consumes `grlift_homology` quotient instances).
/-- The file-6 master: dimension equation + R2 exactness from the sop data.
conditional-exact on `[hker⊥, GrLiftIntertwining, GrLiftFiltrationConseq]`. -/
theorem grlift_master (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (hint : GrLiftIntertwining P d g hgen
      (grlift_grEquivOfKerEqBot P d g hgen hker))
    (hfiltr : GrLiftFiltrationConseq P d g hgen) :
    ringKrullDim (Localization.AtPrime P) = d ∧
      ∀ j, contractExactAt (koszulContractOfSequence g) j :=
  ⟨grlift_dim_eq_of_sop P d g hgen hd,
    grlift_r2_exact P d g hgen hker hint hfiltr⟩

#print axioms grlift_sop_full
#print axioms grlift_grExact_of_intertwining
#print axioms grlift_exact_of_grConsequence
#print axioms grlift_r2_exact

end GradedLift
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-
Downstream note (proof lane, N2 discharge): `filtr_grlift_conseq_unconditional`
(`LeadingTermMaps.lean`) proves `GrLiftFiltrationConseq` from `hgen` alone, so
the reduced masters (`grlift_r2_exact_of_equiv` minus `hfiltr`,
`grlift_r2_exact` on `[hker, hint]`, `grlift_master` on `[hker, hint]`)
elaborate downstream of both files (prototype verified: axioms
`[propext, Classical.choice, Quot.sound]`; `FRL P` is a reducible abbrev for
`Localization.AtPrime P`, so the `hgen` binders match by defeq with no bridge).
They are not stated here: `LeadingTermMaps` imports this file, so importing the
N2 master back would be an import cycle. Land them in `LeadingTermMaps.lean`
(or a new module importing both), not here.
-/
