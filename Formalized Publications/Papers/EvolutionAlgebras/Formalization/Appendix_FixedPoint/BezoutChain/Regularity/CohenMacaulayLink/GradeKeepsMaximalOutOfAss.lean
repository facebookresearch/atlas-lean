/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Maps
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.FirstRegularLengthOne
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.DimLeGradeRegular
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMDepthSubstitution
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.RegularRingFoundation
import Mathlib.RingTheory.Regular.RegularSequence
/-!
# R2: positive grade keeps `𝔪` out of `Ass`

Contrapositive of the grade-zero lemma
`GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes` (`GradeDepthFragment.lean`).
Feeds L-AVOID (`firstReg_of_maximalIdeal_notMem_ass`,
`FirstRegularLengthOne.lean`) in the R5 chain.

Repairs applied: Repair 1 (`by decide` replaced by
`one_ne_zero (le_antisymm …)` since `ℕ∞` has no decidable order). The design note's
`Module.associatedPrimes` prefix is stated as the root `associatedPrimes`:
in this mathlib version `Module.associatedPrimes` is a lemma namespace, not
the set (`Unknown constant` if used as a term), and the root name is what
both the grade-zero lemma and L-AVOID consume.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradePosNotMemAssR2

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain

/-- R2: positive grade keeps `𝔪` out of `Ass` (contrapositive of
`GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes`). The `IsLocalRing` /
`IsNoetherianRing` hypotheses are unused by the proof; they match the R5
call-site context so R5 applies this without instance friction. -/
theorem maximalIdeal_notMem_associatedPrimes_of_one_le_grade
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (h : 1 ≤ GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S)) :
    IsLocalRing.maximalIdeal S ∉ associatedPrimes S S := by
  intro hmem
  have h0 := GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes (R := S) (M := S) hmem
  rw [h0] at h
  exact one_ne_zero (le_antisymm h zero_le)

#print axioms maximalIdeal_notMem_associatedPrimes_of_one_le_grade

end GradePosNotMemAssR2
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# R3: non-zero-dimensional Noetherian rings have `1 ≤ ringKrullDim`

`Ring.krullDimLE_iff`
(`Basic.lean`) + `lt_of_not_ge`, then the `WithBot` destructure-and-coerce
idiom (`GradeDepthFragment.lean`). Feeds the grade side of the R5 chain.

Repairs applied: Repair 2 (`ENat.one_le_iff_ne_zero` replaced by the
non-deprecated `Order.one_le_iff_ne_zero`) and Repair 3 (pin citation
`432-434` → `432-435`); additionally the `≠ ⊥` step routes through
`⊥ ≤ 0` (`ne_of_gt` alone gives `≠ 0`, not `≠ ⊥`), the destructure rewrite
uses `← hd` (`hd : ↑d = ringKrullDim S`, cf. `GradeDepthFragment.lean`), and the
`↑0` cast is normalized by `Nat.cast_zero` (all anticipated by the verdict).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KrullDimPosOfNotDimLER3

/-- R3: non-zero-dimensional rings have `1 ≤ ringKrullDim`. No `Nontrivial`
hypothesis is needed: it is derived from `h` via
`ringKrullDim_eq_bot_of_subsingleton` (`Basic.lean`). The
`IsNoetherianRing` hypothesis matches the R5 call-site context. -/
theorem one_le_ringKrullDim_of_not_krullDimLE_zero
    (S : Type*) [CommRing S] [IsNoetherianRing S]
    (h : ¬ Ring.KrullDimLE 0 S) :
    1 ≤ ringKrullDim S := by
  rw [Ring.krullDimLE_iff] at h
  simp only [Nat.cast_zero] at h
  have hlt : (0 : WithBot ℕ∞) < ringKrullDim S := lt_of_not_ge h
  have hD : ringKrullDim S ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hlt)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hD
  rw [← hd] at hlt ⊢
  have hpos : (0 : ℕ∞) < d := WithBot.coe_lt_coe.mp hlt
  exact WithBot.coe_le_coe.mpr (Order.one_le_iff_ne_zero.mpr (ne_of_gt hpos))

#print axioms one_le_ringKrullDim_of_not_krullDimLE_zero

end KrullDimPosOfNotDimLER3
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# R4: a ring equiv between local rings maps `𝔪` to `𝔪`

Comap-first proof via the FRCore pattern
(`Ideal.comap_isMaximal_of_surjective` + `IsLocalRing.eq_maximalIdeal`), closed with
`Ideal.map_comap_of_surjective`. Discharges the `hmap` hypothesis of
`isCM_ringEquiv_congr` (`CMPositiveDimHasDepth.lean`) unconditionally.

Repairs applied: Repair 4 (comap-first route promoted to primary since
`Ideal.mem_map_iff` does not exist) and Repair 5 (correct name
`Ideal.map_comap_of_surjective`, `Maps.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MaxIdealMapOfRingEquivR4

/-- R4: a ring equiv between local rings maps `𝔪` to `𝔪` (comap is maximal
along the surjective underlying hom, hence equals `𝔪` by uniqueness; map of
comap along a surjection is the identity). -/
theorem maximalIdeal_map_of_ringEquiv
    {S T : Type*} [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]
    (e : S ≃+* T) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal S)
      = IsLocalRing.maximalIdeal T := by
  have hsurj : Function.Surjective ⇑e.toRingHom :=
    fun t => ⟨e.symm t, e.apply_symm_apply t⟩
  have hcomap : (IsLocalRing.maximalIdeal T).comap e.toRingHom
      = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective e.toRingHom hsurj)
  calc Ideal.map e.toRingHom (IsLocalRing.maximalIdeal S)
      = Ideal.map e.toRingHom ((IsLocalRing.maximalIdeal T).comap e.toRingHom) := by
        rw [hcomap]
    _ = IsLocalRing.maximalIdeal T := Ideal.map_comap_of_surjective e.toRingHom hsurj _

#print axioms maximalIdeal_map_of_ringEquiv

end MaxIdealMapOfRingEquivR4
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# R5: `FRCore` unconditional — the CM route
Proves `frCore_unconditional`: for a
proper CI quotient `T = R_Q ⧸ span(rs₀)` of length `≥ 2` and any abstract
local `S ≃+* T` of positive dimension, `𝔪_S ∉ Ass(S)`.

## Route (the 11-step R5 chain)

1. Steps 1-2: `R_Q` is regular local (`regLocal_atPrime`, via
   `IsRegularRing` of `K[X]` localizing).
2. C1 side condition: `dim R_Q < ⊤` (`dim_atPrime_lt_top`).
3. R1: `↑grade = dim` for `R_Q` (`grade_eq_dim_of_isRegularLocal`,
   Matsumura, *Commutative Ring Theory*, Th 17.8 as formalized by
   `DimLeGradeRegular`), which is the C2 `IsCM` body by def.
4. Locality: `span(rs₀) ≤ 𝔪` gives `[IsLocalRing T]`
   (`hC2loc_discharged`).
5. L6: CM descends along the regular-sequence quotient
   (`isCM_quotient_span_of_isRegular_subst`, the C2 main step iterated).
6. C2→C3 bridge (`isCM_c3_of_c2`, `rfl`).
7. R4 at `e.symm`: the equiv maps `𝔪_T` to `𝔪_S`
   (`maximalIdeal_map_of_ringEquiv`).
8. Transport: `IsCM` across `e.symm` (R-A local copy below).
9. R3: `¬KrullDimLE 0 S → 1 ≤ dim S`
   (`one_le_ringKrullDim_of_not_krullDimLE_zero`).
10. The CM equation turns `1 ≤ dim` into `1 ≤ grade`.
11. R2: positive grade keeps `𝔪` out of `Ass`
    (`maximalIdeal_notMem_associatedPrimes_of_one_le_grade`).

`hlen` is unused: the CM route needs no length floor, so R5 proves a
stronger statement than `FRCore`. The `frCore_of_b1_of_b2cExists` stays
as the gated predecessor.

## Repairs applied (assembly verdict)

* R-A (load-bearing): `CMPositiveDimHasDepth.isCM_ringEquiv_congr` is
  single-universe, but R5 applies it across `T : Type uK`, `S : Type uS`.
  The verdict's fix (generalize that signature) touches a proved file, so
  per the fresh-files-only rule it is localized here as
  `isCM_ringEquiv_congr_univ` with `{A B : Type*}`: the proof body is
  copied verbatim and is universe-clean (all ingredients —
  `AddEquiv.isRegular_congr`, `ringKrullDim_eq_of_ringEquiv`, both `IsCM`
  defs, Ideal/List ops — are `Type*`-polymorphic).
* R-B: the full intro pattern (instance binders kept).
* R-C: root `regLocal_atPrime` (`RegularRingFoundation` declares no namespace).
-/

universe uK uS

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradeKeepsMaximalOutOfAss

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain

/-- R-A repair (localized): `IsCM` transports across a ring equivalence
preserving the maximal ideal, at independent universes. Verbatim copy of
`CMPositiveDimHasDepth.isCM_ringEquiv_congr` (`CMPositiveDimHasDepth.lean`)
with `{A B : Type u}` generalized to `{A B : Type*}`; the proof body is
universe-clean (Matsumura CM-preservation under isomorphism, via grade-set
congruence plus `ringKrullDim` congruence). -/
theorem isCM_ringEquiv_congr_univ {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B)
    (hmap : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A)
      = IsLocalRing.maximalIdeal B)
    (hCM : CMPositiveDimHasDepth.IsCM A) : CMPositiveDimHasDepth.IsCM B := by
  have hmaxB : (IsLocalRing.maximalIdeal B).IsMaximal := inferInstance
  have hne : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap]
    exact hmaxB.ne_top
  have hcc : (Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A)).comap
        e.toRingHom
      = IsLocalRing.maximalIdeal A :=
    Ideal.comap_map_eq_self_of_isMaximal e.toRingHom hne
  have hGradeSet : GradeDepthFragment.GradeSet B B (IsLocalRing.maximalIdeal B)
      = GradeDepthFragment.GradeSet A A (IsLocalRing.maximalIdeal A) := by
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      refine ⟨rs.map ⇑e.symm, by rw [List.length_map]; exact hlen, ?_, ?_⟩
      · intro a ha
        rw [List.mem_map] at ha
        obtain ⟨r, hr, rfl⟩ := ha
        rw [← hcc, Ideal.mem_comap]
        change ⇑e (⇑e.symm r) ∈ Ideal.map e.toRingHom
          (IsLocalRing.maximalIdeal A)
        rw [e.apply_symm_apply, hmap]
        exact hmem r hr
      · have h2 : List.Forall₂
            (fun (b : B) (a : A) => ∀ x,
              e.symm.toAddEquiv (b • x) = a • e.symm.toAddEquiv x)
            rs (rs.map ⇑e.symm) := by
          rw [List.forall₂_map_right_iff, List.forall₂_same]
          intro b _ x
          change ⇑e.symm (b • x) = (⇑e.symm b) • ⇑e.symm x
          rw [smul_eq_mul, smul_eq_mul, map_mul]
        exact (e.symm.toAddEquiv.isRegular_congr h2).mp hreg
    · rintro ⟨rs, hlen, hmem, hreg⟩
      refine ⟨rs.map ⇑e, by rw [List.length_map]; exact hlen, ?_, ?_⟩
      · intro b hb
        rw [List.mem_map] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        rw [← hmap]
        exact Ideal.mem_map_of_mem e.toRingHom (hmem a ha)
      · have h2 : List.Forall₂
            (fun (a : A) (b : B) => ∀ x,
              e.toAddEquiv (a • x) = b • e.toAddEquiv x)
            rs (rs.map ⇑e) := by
          rw [List.forall₂_map_right_iff, List.forall₂_same]
          intro a _ x
          change ⇑e (a • x) = (⇑e a) • ⇑e x
          rw [smul_eq_mul, smul_eq_mul, map_mul]
        exact (e.toAddEquiv.isRegular_congr h2).mp hreg
  have hgrade : GradeDepthFragment.grade B B (IsLocalRing.maximalIdeal B)
      = GradeDepthFragment.grade A A (IsLocalRing.maximalIdeal A) := by
    unfold GradeDepthFragment.grade
    rw [hGradeSet]
  have hdim : ringKrullDim B = ringKrullDim A :=
    ringKrullDim_eq_of_ringEquiv e.symm
  unfold CMPositiveDimHasDepth.IsCM at hCM ⊢
  rw [hgrade, hdim]
  exact hCM

#print axioms isCM_ringEquiv_congr_univ

set_option maxSynthPendingDepth 3 in
/-- R5: `FRCore` unconditional (Matsumura Th 17.8 CM route: regular local
`R_Q` is CM; CM descends along the regular-sequence quotient to `T`;
transport to `S`; positive dimension forces positive grade, hence
`𝔪 ∉ Ass`). Stronger than stated: no length floor is used. -/
theorem frCore_unconditional : FirstRegularLengthOne.FRCore.{uK, uS} := by
  intro m K _ Q _ S _ _ _ rs₀ _hlen hmem hreg hne hpos
  obtain ⟨e⟩ := hne
  -- Step 1 (Steps 1-2): `R_Q` is regular local.
  have hregQ := regLocal_atPrime K Q
  -- Step 2 (C1 side condition): `dim R_Q < ⊤`.
  have hfinQ := DimLeGradeRegular.dim_atPrime_lt_top m K Q
  -- Step 3 (R1, is C2 `IsCM` by def): `↑grade = dim` for `R_Q`.
  have hCMQ : QuotientByRegularIsCM.IsCM (Localization.AtPrime Q) :=
    DimLeGradeRegular.grade_eq_dim_of_isRegularLocal _ hfinQ hregQ
  -- Step 4 (locality): `span(rs₀) ≤ 𝔪` gives `[IsLocalRing T]`.
  have hle : Ideal.span {x | x ∈ rs₀} ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    Ideal.span_le.mpr (fun x hx => hmem x hx)
  have _hlocalT := CMDepthSubstitution.hC2loc_discharged _ hle
  -- Step 5 (L6): CM descends to `T`.
  have hCMT : QuotientByRegularIsCM.IsCM
      ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}) :=
    CMDepthSubstitution.isCM_quotient_span_of_isRegular_subst rs₀ hmem
      hreg hCMQ
  -- Step 6 (C2→C3 bridge).
  have hCMT3 := CMDepthSubstitution.isCM_c3_of_c2 hCMT
  -- Step 7 (R4 at `e.symm`).
  have hmap := MaxIdealMapOfRingEquivR4.maximalIdeal_map_of_ringEquiv
    (S := (Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}) (T := S) e.symm
  -- Step 8 (transport across `e.symm`, R-A local copy).
  have hCMS : CMPositiveDimHasDepth.IsCM S :=
    isCM_ringEquiv_congr_univ e.symm hmap hCMT3
  -- Step 9 (R3): `1 ≤ dim S`.
  have h1dim :=
    KrullDimPosOfNotDimLER3.one_le_ringKrullDim_of_not_krullDimLE_zero S hpos
  -- Step 10 (CM equation turns `1 ≤ dim` into `1 ≤ grade`).
  have hCMSeq : ((GradeDepthFragment.grade S S (IsLocalRing.maximalIdeal S) : ℕ∞) :
      WithBot ℕ∞) = ringKrullDim S := hCMS
  rw [← hCMSeq, ← WithBot.coe_one] at h1dim
  have h1grade := WithBot.coe_le_coe.mp h1dim
  -- Step 11 (R2): positive grade keeps `𝔪` out of `Ass`.
  exact GradePosNotMemAssR2.maximalIdeal_notMem_associatedPrimes_of_one_le_grade
    S h1grade

#print axioms frCore_unconditional

end GradeKeepsMaximalOutOfAss
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# `FirstReg` full discharge
Proves `firstReg_unconditional`: every
proper CI quotient of positive dimension carries a regular element in its
maximal ideal.

## Case split (mirror of the L5 head (ii), minus the dropped-`≠[]`/nil case)

* `rs₀ = []`: contradicts `hne`.
* `rs₀ = [x]`: FR1 (`firstReg_length_one`).
* `rs₀ = x :: y :: tl₂`: FRCore (`frCore_unconditional`) yields
  `𝔪 ∉ Ass`, closed by L-AVOID
  (`firstReg_of_maximalIdeal_notMem_ass`, prime avoidance in the
  Matsumura, *Commutative Ring Theory*, Th 12.1 tradition per
  `SystemOfParametersExistence`).

Fresh file, not appended to `FirstRegularLengthOne.lean` (that would be
circular, since R5 imports it).

## Repairs applied (assembly verdict)

* R-D: L5-style `revert hne hmem hreg hNonempty` before `cases` (keeping
  `hpos`, which does not mention `rs₀`) plus per-branch intros.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace FirstRegAssemble

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain

/-- `FirstReg` unconditional: the `r = 1` case is FR1, the `r ≥ 2` case is
FRCore (R5, the Matsumura Th 17.8 CM route) closed by prime-avoidance
L-AVOID. -/
theorem firstReg_unconditional
    : CMQuotientFull.FirstReg.{uK, uS} := by
  intro m K _ Q _ S _ _ _ rs₀ hne hmem hreg hNonempty hpos
  revert hne hmem hreg hNonempty
  cases rs₀ with
  | nil =>
    intro hne _hmem _hreg _hNonempty
    exact absurd rfl hne
  | cons x tl =>
    cases tl with
    | nil =>
      intro _hne hmem hreg hNonempty
      obtain ⟨e⟩ := hNonempty
      have hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
        hmem x (by simp)
      exact FirstRegularLengthOne.firstReg_length_one m K Q S x hx hreg e hpos
    | cons y tl2 =>
      intro _hne hmem hreg hNonempty
      have hlen : 2 ≤ (x :: y :: tl2).length := by
        simp only [List.length_cons]
        omega
      have hmax := GradeKeepsMaximalOutOfAss.frCore_unconditional m K Q S
        (x :: y :: tl2) hlen hmem hreg hNonempty hpos
      exact FirstRegularLengthOne.firstReg_of_maximalIdeal_notMem_ass S hmax

#print axioms firstReg_unconditional

end FirstRegAssemble
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
