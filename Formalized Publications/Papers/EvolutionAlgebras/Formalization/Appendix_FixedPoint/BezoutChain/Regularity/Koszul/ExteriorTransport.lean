/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ContractionFormula
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.PolynomialExactness
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerIdentification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.Fin.Basic

/-!
# Cross-ring exterior transport for the gr-lift (A4(iii), missing-2 bridge)

This file builds the degree-wise exterior bijections `E k` across the ring
change that `GrLiftIntertwining` (`GradedLift.lean`) consumes, from the
proved L3/L4 parts. It states the bridge as an explicit `Prop` in §1 and
proves it in §5.

* (§1) `ExtTransportBridge`: the near-minimal bridge — existence of degree-wise
  plain bijections `⋀[S]^k (towerMod) ≃ ⋀[T]^k (Fin d → T)` that are additive,
  send `c • x` to `σ c • E x`, and send `ιMulti v` to `ιMulti (e ∘ v)` for the
  proved degree-1 transport `e = towerPiSemilinear`. Plus the span-induction
  helper and the `ιMulti`-form contraction formula used to consume it.
* (§2) `extTransport_contract_comm`: the bridge + functional compatibility
  (`φT (e x) = σ (φS x)`) give the full `E`-part of `GrLiftIntertwining`
  (`E k 0 = 0` + commutation with `koszulContract` on both sides), by span
  induction against the alternating-sum formula. `extTransport_unique` shows
  the laws determine `E` uniquely.
* (§3) Functional compatibility from the generator correspondence:
  `towerPhi_top_sum` (the tower functional in pi-coordinates),
  `koszulContractOfSequence_apply_sum` (the sequence functional in
  coordinates), and `extTransport_phi_compat_of_X`.
* (§4) `extTransport_grLift_E`: the GrLift-ready `E`-part, conditional on
  `[ExtTransportBridge, hX]`. The consumer instantiates `T := grRegular P`,
  `σ := hgrEquiv`, `x := grlift_grClass`, discharging `hX` by the proved
  `grlift_grEquiv_comp` (`GradedLift.lean`); the augmentation data
  (`εgr`, `τ`) of `GrLiftIntertwining` stays residual (out of scope here).

Design: no semilinear `AlternatingMap` is built (refuted route — Mathlib has
no semilinear exterior-power functor). The bridge instead axiomatizes the
*values* of the transport (add/smul/`ιMulti` laws) as a plain-`Equiv`
existential, and every consequence (commutation, uniqueness, φ-compat) is
proved from those laws. This file does not import `GradedLift` (so the
consumer can import it without a cycle); the GrLift wiring is a one-line
instantiation documented at `extTransport_grLift_E`.

## References

Project (all read-only):
* `Regularity/Koszul/GradedLift.lean`: `GrLiftIntertwining` (:310), `grlift_phiGr`
  (:224), `grlift_grClass` (:213), `grlift_grEquiv_comp` (:374) (consumer;
  not imported).
* `Regularity/HomologicalDepth/TowerIdentification.lean`: `towerModEquivTop` (:145),
  `towerExtEquiv` (:152), `towerPiSemilinear` (:220),
  `piFinSemilinear_apply` (:191), `snocLinearEquiv_apply` (:123).
* `Regularity/Koszul/ContractionFormula.lean`:
  `koszulContract_exteriorPower_ιMulti` (:223), `contractLeft_ιMulti` (:144),
  `exteriorPower_semilinear_ext` (:74, induction pattern).
* `Regularity/Koszul/PolynomialExactness.lean`: `towerMod` (:440), `towerPhi` (:457),
  `towerPhi_succ` (:468), `rungScalar` (:204), `rungScalar_eq` (:211).
* `Regularity/Koszul/KoszulComplex.lean`: `koszulContract` (:346),
  `koszulContractOfSequence` (:455).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `LinearAlgebra/ExteriorPower/Basic.lean`: `ιMulti` (:56), `ιMulti_span`
  (:108), `map` (:260), `map_apply_ιMulti` (:273).
* `LinearAlgebra/Span/Defs.lean`: `Submodule.span_induction` (via
  `ContractionFormula.lean`).
* `Algebra/BigOperators/Fin.lean`: `prod_univ_castSucc` (:84, `to_additive`
  `sum_univ_castSucc`).
* `LinearAlgebra/Basis/Defs.lean`: `Module.Basis.constr_apply_fintype` (:563).
* `LinearAlgebra/StdBasis.lean`: `basisFun_equivFun` (:134).
* `Algebra/Module/Equiv/Defs.lean`: `refl_apply` (:246), `trans_apply` (:346).
* `LinearAlgebra/Prod.lean`: `prodCongr_apply` (:780).

## Status

* §1 helpers (`extTransport_span_induction`, `extTransport_map_sum`,
  `koszulContract_ιMulti_extPow`): unconditional.
* §2 `extTransport_contract_comm`: conditional-exact on
  `[ExtTransportBridge, hφ]`; `extTransport_unique`: unconditional.
* §3 (`towerPhi_sum_aux`, `towerPhi_top_sum`,
  `koszulContractOfSequence_apply_sum`, `extTransport_phi_compat_of_X`):
  unconditional.
* §4 `extTransport_grLift_E`: conditional-exact on
  `[ExtTransportBridge, hX]`.
* §5: `ExtTransportBridge` is proved (`extTransportBridge_proved`).
  The `GrLiftIntertwining` augmentation data (`εgr`, `τ`) stays residual.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ExteriorTransport

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PolynomialExactness
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerIdentification
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ContractionFormula
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex

variable (κ : Type*) [Field κ] (d : ℕ)

/-! ## §1. The bridge and its consumption helpers -/

/-- The degree-wise exterior lift of the tower-to-pi semilinear transport
`towerPiSemilinear` across a ring equivalence `σ : S ≃+* T`
(where `S = MvPolynomial (Fin d) κ`).

The transport is specified by its values, as plain bijections: `0 ↦ 0`
(redundant: follows from additivity), additivity, `E k (c • x) = σ c • E k x`,
`E k (ιMulti v) = ιMulti (fun i => e (v i))` on decomposable wedges. This is
the exterior-of-a-semilinear-map existence statement; Mathlib has no
semilinear exterior-power functor (`exteriorPower.map` is linear-only), so it
is stated as an explicit `Prop` and proved in §5
(`extTransportBridge_proved`). -/
def ExtTransportBridge (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) : Prop :=
  ∃ E : ∀ k : ℕ,
      ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
        ↥(⋀[T]^k (Fin d → T)),
    (∀ k, E k 0 = 0) ∧
    (∀ k x y, E k (x + y) = E k x + E k y) ∧
    (∀ k (c : MvPolynomial (Fin d) κ) x, E k (c • x) = (σ c) • E k x) ∧
    ∀ k (v : Fin k → towerMod κ d d),
      E k (exteriorPower.ιMulti _ _ v) =
        exteriorPower.ιMulti _ _ fun i => (towerPiSemilinear κ d T σ) (v i)

/-- Span induction for plain predicates on an exterior power: to prove `P` of
every element it suffices to check `0`, closure under `+`/`•`, and the
`ιMulti` generators. Same pattern as `exteriorPower_semilinear_ext`
(`ContractionFormula.lean`).
-/
theorem extTransport_span_induction {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] {k : ℕ} {P : ↥(⋀[S]^k M) → Prop}
    (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : S) x, P x → P (c • x))
    (hgen : ∀ v : Fin k → M, P (exteriorPower.ιMulti S k v)) :
    ∀ x, P x := by
  intro x
  have hspan := exteriorPower.ιMulti_span S k M
  have hx : x ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S k (M := M))) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact hgen v
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul r y _ hy => exact hsmul r y hy

/-- A bridge transport pushes through finite sums (from `0 ↦ 0` + additivity).
-/
theorem extTransport_map_sum (T : Type*) [CommRing T]
    (E : ∀ k : ℕ, ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
      ↥(⋀[T]^k (Fin d → T)))
    (k : ℕ) (hE0 : E k 0 = 0)
    (hadd : ∀ x y, E k (x + y) = E k x + E k y)
    {ι : Type*} (s : Finset ι)
    (f : ι → ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d))) :
    E k (∑ i ∈ s, f i) = ∑ i ∈ s, E k (f i) := by
  classical
  refine Finset.induction ?_ ?_ s
  · simp only [Finset.sum_empty]
    exact hE0
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

/-- The bundled contraction on `exteriorPower.ιMulti` generators, with the
summands also in `exteriorPower.ιMulti` form. Definitionally equal to
`koszulContract_exteriorPower_ιMulti` (whose summands use the anonymous
constructor); restated so bridge rewrites fire syntactically.
-/
theorem koszulContract_ιMulti_extPow {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (n : ℕ) (v : Fin n.succ → M) :
    koszulContract φ n (exteriorPower.ιMulti R n.succ v) =
      ∑ j : Fin n.succ, ((-1 : R) ^ (j.val) * φ (v j)) •
        exteriorPower.ιMulti R n (v ∘ Fin.succAbove j) :=
  koszulContract_exteriorPower_ιMulti φ n v

/-! ## §2. Commutation and uniqueness from the bridge -/

/-- Missing-2 `E`-part from the bridge: the transported bijections commute
with the Koszul contractions, given functional compatibility
(`φT (e x) = σ (φS x)`). By span induction
(`extTransport_span_induction`): the `0`/`+`/`•` cases close by the bridge
laws, and the generator case is the alternating-sum formula
(`koszulContract_ιMulti_extPow`) on both sides plus `hφ`.

Conditional on exactly `[ExtTransportBridge, hφ]`. -/
theorem extTransport_contract_comm (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T)
    (φS : (towerMod κ d d) →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ)
    (φT : (Fin d → T) →ₗ[T] T)
    (hbridge : ExtTransportBridge κ d T σ)
    (hφ : ∀ x : towerMod κ d d,
      φT ((towerPiSemilinear κ d T σ) x) = σ (φS x)) :
    ∃ E : ∀ k : ℕ,
        ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
          ↥(⋀[T]^k (Fin d → T)),
      (∀ k, E k 0 = 0) ∧
      ∀ k (w : ↥(⋀[MvPolynomial (Fin d) κ]^(k + 1) (towerMod κ d d))),
        E k (koszulContract φS k w) =
          koszulContract φT k (E (k + 1) w) := by
  obtain ⟨E, hE0, hadd, hsmul, hι⟩ := hbridge
  refine ⟨E, hE0, fun k => ?_⟩
  apply extTransport_span_induction
  · rw [map_zero, hE0 k, hE0 (k + 1), map_zero]
  · intro x y hx hy
    rw [map_add, hadd k, hadd (k + 1), map_add, hx, hy]
  · intro r y hy
    rw [map_smul, hsmul k, hsmul (k + 1), map_smul, hy]
  · intro v
    change E k (koszulContract φS k (exteriorPower.ιMulti _ k.succ v)) =
      koszulContract φT k (E k.succ (exteriorPower.ιMulti _ k.succ v))
    rw [koszulContract_ιMulti_extPow φS k v]
    rw [extTransport_map_sum κ d T E k (hE0 k) (hadd k) Finset.univ _]
    simp only [hsmul k, hι k]
    rw [hι k.succ v, koszulContract_ιMulti_extPow φT k _]
    apply Finset.sum_congr rfl
    intro j _
    have hσneg : ∀ m : ℕ,
        σ ((-1 : MvPolynomial (Fin d) κ) ^ m) = (-1 : T) ^ m := by
      intro m
      rw [map_pow]
      congr 1
      simp
    have hcoeff : σ ((-1 : MvPolynomial (Fin d) κ) ^ j.val * φS (v j)) =
        (-1 : T) ^ j.val *
          φT ((fun i => (towerPiSemilinear κ d T σ) (v i)) j) := by
      rw [map_mul, hσneg, ← hφ (v j)]
    have harg : (fun i => (towerPiSemilinear κ d T σ) ((v ∘ Fin.succAbove j) i)) =
        (fun i => (towerPiSemilinear κ d T σ) (v i)) ∘ Fin.succAbove j := rfl
    rw [hcoeff, harg]

/-- The bridge laws determine the transport: any two families satisfying
the add/smul/`ιMulti` laws agree. -/
theorem extTransport_unique (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T)
    (E E' : ∀ k : ℕ, ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
      ↥(⋀[T]^k (Fin d → T)))
    (hE0 : ∀ k, E k 0 = 0) (hE0' : ∀ k, E' k 0 = 0)
    (hadd : ∀ k x y, E k (x + y) = E k x + E k y)
    (hadd' : ∀ k x y, E' k (x + y) = E' k x + E' k y)
    (hsmul : ∀ k (c : MvPolynomial (Fin d) κ) x, E k (c • x) = (σ c) • E k x)
    (hsmul' : ∀ k (c : MvPolynomial (Fin d) κ) x, E' k (c • x) = (σ c) • E' k x)
    (hι : ∀ k (v : Fin k → towerMod κ d d),
      E k (exteriorPower.ιMulti _ _ v) =
        exteriorPower.ιMulti _ _ fun i => (towerPiSemilinear κ d T σ) (v i))
    (hι' : ∀ k (v : Fin k → towerMod κ d d),
      E' k (exteriorPower.ιMulti _ _ v) =
        exteriorPower.ιMulti _ _ fun i => (towerPiSemilinear κ d T σ) (v i)) :
    ∀ k, E k = E' k := by
  intro k
  apply Equiv.ext
  apply extTransport_span_induction
  · rw [hE0 k, hE0' k]
  · intro a b ha hb
    rw [hadd k, hadd' k, ha, hb]
  · intro c y hy
    rw [hsmul k, hsmul' k, hy]
  · intro v
    rw [hι k, hι' k]

/-! ## §3. Functional compatibility from the generator correspondence -/

/-- The tower functional in pi-coordinates: `towerPhi` is the dot product with
the rung scalars along `towerModEquiv`. HilbertFunctionCount on `n`, splitting the sum
at the snoc end (`Fin.sum_univ_castSucc`).
-/
theorem towerPhi_sum_aux (n : ℕ) (hn : n ≤ d) (q : towerMod κ d n) :
    towerPhi κ d n q =
      ∑ i : Fin n, rungScalar κ d i.val * ((towerModEquiv κ d n) q) i := by
  revert hn q
  induction n with
  | zero =>
    intro _ q
    have h0 : towerPhi κ d 0 = 0 := rfl
    rw [h0]
    simp
  | succ n ih =>
    intro hn q
    have hn' : n ≤ d := Nat.le_of_succ_le hn
    rw [towerPhi_succ, Fin.sum_univ_castSucc]
    simp only [towerModEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, snocLinearEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last]
    rw [ih hn' q.1]

/-- The top tower functional is the dot product with the variables along
`towerModEquivTop` (rung scalars at `i.val < d` are the variables).
-/
theorem towerPhi_top_sum (q : towerMod κ d d) :
    towerPhi κ d d q =
      ∑ i : Fin d, MvPolynomial.X i * ((towerModEquivTop κ d) q) i := by
  have h := towerPhi_sum_aux κ d d (le_refl d) q
  have hrung : ∀ i : Fin d, rungScalar κ d i.val = MvPolynomial.X i := by
    intro i
    rw [rungScalar_eq κ d i.val i.2]
    simp only [rungVar]
  change towerPhi κ d d q =
    ∑ i : Fin d, MvPolynomial.X i * ((towerModEquiv κ d d) q) i
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrung i]

/-- The Koszul sequence-functional in coordinates: evaluation is the dot
product. Via `Module.Basis.constr_apply_fintype` + `Pi.basisFun_equivFun`.
-/
theorem koszulContractOfSequence_apply_sum (T : Type*) [CommRing T]
    (x : Fin d → T) (f : Fin d → T) :
    koszulContractOfSequence x f = ∑ i, x i * f i := by
  simp only [koszulContractOfSequence, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, mul_comm]

/-- Functional compatibility from the generator correspondence: the
sequence-functional intertwines `towerPhi` along `towerPiSemilinear` when `σ`
sends each variable to the corresponding sequence entry. From
`towerPhi_top_sum` + `koszulContractOfSequence_apply_sum`.
-/
theorem extTransport_phi_compat_of_X (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (x : Fin d → T)
    (hX : ∀ i, σ (MvPolynomial.X i) = x i) (q : towerMod κ d d) :
    koszulContractOfSequence x ((towerPiSemilinear κ d T σ) q) =
      σ (towerPhi κ d d q) := by
  rw [koszulContractOfSequence_apply_sum, towerPhi_top_sum κ d q, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [towerPiSemilinear, LinearEquiv.trans_apply, piFinSemilinear_apply]
  rw [map_mul, hX i]

/-! ## §4. The GrLift-ready `E`-part -/

/-- GrLift-ready `E`-part: the degree-wise exterior bijections across the ring
change, commuting with the file-5 tower contraction and a sequence
contraction, from the bridge + the generator correspondence.

The consumer (`GrLiftIntertwining`, `GradedLift.lean`) instantiates
`T := grRegular P`, `σ := hgrEquiv`, `x:= fun i => grlift_grClass P d g hgen
i`, discharging `hX` by the proved `grlift_grEquiv_comp`
(`GradedLift.lean`); the augmentation data (`εgr`, `τ`) stays residual.

Conditional on exactly `[ExtTransportBridge, hX]`. -/
theorem extTransport_grLift_E (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (x : Fin d → T)
    (hX : ∀ i, σ (MvPolynomial.X i) = x i)
    (hbridge : ExtTransportBridge κ d T σ) :
    ∃ E : ∀ k : ℕ,
        ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
          ↥(⋀[T]^k (Fin d → T)),
      (∀ k, E k 0 = 0) ∧
      ∀ k (w : ↥(⋀[MvPolynomial (Fin d) κ]^(k + 1) (towerMod κ d d))),
        E k (koszulContract (towerPhi κ d d) k w) =
          koszulContract (koszulContractOfSequence x) k (E (k + 1) w) :=
  extTransport_contract_comm κ d T σ (towerPhi κ d d)
    (koszulContractOfSequence x) hbridge
    (extTransport_phi_compat_of_X κ d T σ x hX)

#print axioms extTransport_contract_comm
#print axioms extTransport_grLift_E
#print axioms extTransport_unique
#print axioms towerPhi_top_sum
#print axioms extTransport_phi_compat_of_X

/-! ## §5. The bridge, proved by exterior-basis transport

Route: transport the exterior bases across the semilinear degree-1 map,
both directions, with the inverse check via ext.
* `piExtTransportFun` / `piExtTransportInvFun`: forward/backward maps on
  `⋀^k (Fin d → ·)` across `σ` / `σ.symm`, via the exterior bases
  `Module.Basis.exteriorPower` of `Pi.basisFun` and coefficientwise
  `Finsupp.mapRange`.
* `piExtTransport`: the bundled `Equiv`; inverse checks by `Finsupp.ext`
  plus `LinearEquiv` round-trips.
* `piExtTransport_ιMulti`: the generator law, by `repr`-injectivity:
  both sides' coordinates are determinants, and `σ` pushes through
  `det` (`RingEquiv.map_det`).
* `extTransportBridge_proved`: composition with the proved linear part
  `towerExtEquiv`.
-/

/-- Forward coefficient transport on pi-module exterior powers: apply `σ`
to the exterior-basis coordinates for the `Pi.basisFun` exterior basis
(`Module.Basis.exteriorPower`). -/
noncomputable def piExtTransportFun (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ))) :
    ↥(⋀[T]^k (Fin d → T)) :=
  ((Pi.basisFun T (Fin d)).exteriorPower k).repr.symm
    (Finsupp.mapRange ⇑σ (map_zero σ)
      (((Pi.basisFun (MvPolynomial (Fin d) κ)
        (Fin d)).exteriorPower k).repr x))

/-- Backward coefficient transport (same construction with `σ.symm`). -/
noncomputable def piExtTransportInvFun (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (y : ↥(⋀[T]^k (Fin d → T))) :
    ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ)) :=
  (((Pi.basisFun (MvPolynomial (Fin d) κ)
    (Fin d)).exteriorPower k).repr.symm
    (Finsupp.mapRange ⇑σ.symm (map_zero σ.symm)
      (((Pi.basisFun T (Fin d)).exteriorPower k).repr y)))

/-- Backward-after-forward is the identity, by `Finsupp.ext`
(`σ.symm ∘ σ`) plus the `repr` round-trips. -/
theorem piExtTransport_left_inv (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ))) :
    piExtTransportInvFun κ d T σ k (piExtTransportFun κ d T σ k x) = x := by
  classical
  simp only [piExtTransportFun, piExtTransportInvFun,
    LinearEquiv.apply_symm_apply]
  have hmap : Finsupp.mapRange ⇑σ.symm (map_zero σ.symm)
        (Finsupp.mapRange ⇑σ (map_zero σ)
          (((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr x)) =
        (((Pi.basisFun (MvPolynomial (Fin d) κ)
          (Fin d)).exteriorPower k).repr x) := by
    ext a
    simp
  rw [hmap, LinearEquiv.symm_apply_apply]

/-- Forward-after-backward is the identity, by `Finsupp.ext`
(`σ ∘ σ.symm`) plus the `repr` round-trips. -/
theorem piExtTransport_right_inv (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (y : ↥(⋀[T]^k (Fin d → T))) :
    piExtTransportFun κ d T σ k (piExtTransportInvFun κ d T σ k y) = y := by
  classical
  simp only [piExtTransportFun, piExtTransportInvFun,
    LinearEquiv.apply_symm_apply]
  have hmap : Finsupp.mapRange ⇑σ (map_zero σ)
        (Finsupp.mapRange ⇑σ.symm (map_zero σ.symm)
          (((Pi.basisFun T (Fin d)).exteriorPower k).repr y)) =
        (((Pi.basisFun T (Fin d)).exteriorPower k).repr y) := by
    ext a
    simp
  rw [hmap, LinearEquiv.symm_apply_apply]

/-- The degree-`k` exterior transport across `σ` on pi-modules, as a plain
`Equiv` (forward/backward coefficient transport). -/
noncomputable def piExtTransport (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ) :
    ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ)) ≃
      ↥(⋀[T]^k (Fin d → T)) where
  toFun := piExtTransportFun κ d T σ k
  invFun := piExtTransportInvFun κ d T σ k
  left_inv := piExtTransport_left_inv κ d T σ k
  right_inv := piExtTransport_right_inv κ d T σ k

/-- `piExtTransport` unfolds to `piExtTransportFun`. -/
@[simp]
theorem piExtTransport_apply (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ))) :
    piExtTransport κ d T σ k x = piExtTransportFun κ d T σ k x :=
  rfl

/-- Applying `repr` after forward transport recovers the `σ`-mapped
coordinates. -/
theorem piExtTransport_repr (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ))) :
    (((Pi.basisFun T (Fin d)).exteriorPower k).repr
      (piExtTransport κ d T σ k x)) =
      Finsupp.mapRange ⇑σ (map_zero σ)
        ((((Pi.basisFun (MvPolynomial (Fin d) κ)
          (Fin d)).exteriorPower k).repr x)) := by
  simp only [piExtTransport_apply, piExtTransportFun,
    LinearEquiv.apply_symm_apply]

/-- Forward transport sends `0` to `0`. -/
theorem piExtTransport_zero (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ) :
    piExtTransport κ d T σ k 0 = 0 := by
  simp [piExtTransport_apply, piExtTransportFun]

/-- Forward transport is additive. -/
theorem piExtTransport_add (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x y : ↥(⋀[MvPolynomial (Fin d) κ]^k
      (Fin d → MvPolynomial (Fin d) κ))) :
    piExtTransport κ d T σ k (x + y) =
      piExtTransport κ d T σ k x + piExtTransport κ d T σ k y := by
  classical
  have hadd : Finsupp.mapRange ⇑σ (map_zero σ)
        ((((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr x) +
          (((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr y)) =
        Finsupp.mapRange ⇑σ (map_zero σ)
          ((((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr x)) +
        Finsupp.mapRange ⇑σ (map_zero σ)
          ((((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr y)) := by
    ext a
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply, map_add]
  simp only [piExtTransport_apply, piExtTransportFun, map_add, hadd]

/-- Forward transport is `σ`-semilinear on scalars. -/
theorem piExtTransport_smul (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (c : MvPolynomial (Fin d) κ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ))) :
    piExtTransport κ d T σ k (c • x) =
      (σ c) • piExtTransport κ d T σ k x := by
  classical
  have hsmul : Finsupp.mapRange ⇑σ (map_zero σ)
        (c • ((((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr x))) =
        (σ c) • Finsupp.mapRange ⇑σ (map_zero σ)
          ((((Pi.basisFun (MvPolynomial (Fin d) κ)
            (Fin d)).exteriorPower k).repr x)) := by
    ext a
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
  simp only [piExtTransport_apply, piExtTransportFun, map_smul, hsmul]

/-- Forward transport sends decomposable wedges to decomposable wedges
along the degree-1 semilinear transport, by exterior-basis coordinates:
both sides' coordinates are determinants (`basis_repr_apply`,
`ιMultiDual_apply_ιMulti`), and `σ` pushes through `det`
(`RingEquiv.map_det`), with `Pi.basisFun` coordinates being evaluation
and `piFinSemilinear` acting coordinatewise. -/
theorem piExtTransport_ιMulti (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (v : Fin k → (Fin d → MvPolynomial (Fin d) κ)) :
    piExtTransport κ d T σ k (exteriorPower.ιMulti _ _ v) =
      exteriorPower.ιMulti _ _ ((piFinSemilinear σ d) ∘ v) := by
  classical
  apply ((Pi.basisFun T (Fin d)).exteriorPower k).repr.injective
  rw [piExtTransport_repr]
  ext t
  rw [Finsupp.mapRange_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, σ.map_det]
  refine congrArg Matrix.det ?_
  rw [← Matrix.ext_iff]
  intro i j
  simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    Module.Basis.coord_apply, Pi.basisFun_repr, Function.comp_apply,
    piFinSemilinear_apply]

/-- The proved linear part sends decomposable wedges along
`towerModEquivTop` (via `exteriorPower.mapEquiv`, the file-1 precedent). -/
theorem towerExtEquiv_ιMulti (k : ℕ) (v : Fin k → towerMod κ d d) :
    (towerExtEquiv κ d k) (exteriorPower.ιMulti _ _ v) =
      exteriorPower.ιMulti _ _ ((towerModEquivTop κ d) ∘ v) := by
  simp only [towerExtEquiv, exteriorPower.mapEquiv_apply,
    exteriorPower.map_apply_ιMulti, LinearEquiv.coe_coe]

/-- The degree-1 transports agree: `towerPiSemilinear` is the composite. -/
theorem towerPiSemilinear_apply (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (x : towerMod κ d d) :
    (towerPiSemilinear κ d T σ) x =
      (piFinSemilinear σ d) ((towerModEquivTop κ d) x) :=
  rfl

/-- The full degree-`k` transport: proved linear part followed by
coefficient transport. -/
noncomputable def extBridgeEquiv (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ) :
    ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃
      ↥(⋀[T]^k (Fin d → T)) :=
  (towerExtEquiv κ d k).toEquiv.trans (piExtTransport κ d T σ k)

/-- `extBridgeEquiv` is `piExtTransport` after `towerExtEquiv`. -/
@[simp]
theorem extBridgeEquiv_apply (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d))) :
    extBridgeEquiv κ d T σ k x =
      piExtTransport κ d T σ k ((towerExtEquiv κ d k) x) :=
  rfl

/-- The full transport sends `0` to `0`. -/
theorem extBridgeEquiv_zero (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) :
    ∀ k, extBridgeEquiv κ d T σ k 0 = 0 := by
  intro k
  simp only [extBridgeEquiv_apply, map_zero, piExtTransport_zero]

/-- The full transport is additive. -/
theorem extBridgeEquiv_add (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) :
    ∀ k (x y : ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d))),
      extBridgeEquiv κ d T σ k (x + y) =
        extBridgeEquiv κ d T σ k x + extBridgeEquiv κ d T σ k y := by
  intro k x y
  simp only [extBridgeEquiv_apply, map_add, piExtTransport_add]

/-- The full transport is `σ`-semilinear on scalars. -/
theorem extBridgeEquiv_smul (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) :
    ∀ k (c : MvPolynomial (Fin d) κ)
      (x : ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d))),
      extBridgeEquiv κ d T σ k (c • x) =
        (σ c) • extBridgeEquiv κ d T σ k x := by
  intro k c x
  simp only [extBridgeEquiv_apply, map_smul, piExtTransport_smul]

/-- The full transport sends decomposable wedges along
`towerPiSemilinear` (linear part + coefficient part agree on the
composite degree-1 map). -/
theorem extBridgeEquiv_ιMulti (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) (k : ℕ)
    (v : Fin k → towerMod κ d d) :
    extBridgeEquiv κ d T σ k (exteriorPower.ιMulti _ _ v) =
      exteriorPower.ιMulti _ _
        fun i => (towerPiSemilinear κ d T σ) (v i) := by
  rw [extBridgeEquiv_apply, towerExtEquiv_ιMulti, piExtTransport_ιMulti]
  have hfun : ((piFinSemilinear σ d) ∘ ((towerModEquivTop κ d) ∘ v)) =
      (fun i => (towerPiSemilinear κ d T σ) (v i)) := by
    funext i
    exact (towerPiSemilinear_apply κ d T σ (v i)).symm
  rw [hfun]

/-- The bridge, proved: degree-wise exterior transport across `σ` exists.
Basis route: transport exterior bases across the semilinear degree-1
map, both directions, with the inverse check via ext. -/
theorem extTransportBridge_proved (T : Type*) [CommRing T]
    (σ : MvPolynomial (Fin d) κ ≃+* T) : ExtTransportBridge κ d T σ :=
  ⟨fun k => extBridgeEquiv κ d T σ k, extBridgeEquiv_zero κ d T σ,
    extBridgeEquiv_add κ d T σ, extBridgeEquiv_smul κ d T σ,
    extBridgeEquiv_ιMulti κ d T σ⟩

#print axioms extTransportBridge_proved

end ExteriorTransport
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
