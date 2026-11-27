/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CartierStructureConstants.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece
public import MathlibExt.RingTheory.MvFormalGroup.Cartier.BaseChange
public import MathlibExt.RingTheory.MvFormalGroup.Cartier.IntVerschiebung
public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData

/-!
# Structure constants of Cartier modules

Base change compatibilities of the integral Verschiebung and of `V`-adic expansions and, for a
formal `O_D`-module, homogeneous `V`-bases (`FormalODModule.IsHomogeneousVBasis`) and structure
constants of `ϖ` in such a basis (`FormalODModule.HasStructureConstants`), with their behavior
under base change.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

namespace WittLaw

omit hp in
theorem map_coe_map_intCastRingHom {σ : Type*} (f : R →+* S) (Q : MvPolynomial σ ℤ) :
    MvPowerSeries.map f (((MvPolynomial.map (Int.castRingHom R) Q : MvPolynomial σ R)) :
      MvPowerSeries σ R) =
      ((MvPolynomial.map (Int.castRingHom S) Q : MvPolynomial σ S) : MvPowerSeries σ S) := by
  rw [← coe_mvPolynomial_map, MvPolynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom R))
    (Int.castRingHom S)]

theorem map_frobPolyFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (frobPolyFam p R n) = frobPolyFam p S n := by
  rw
      [frobPolyFam_apply, frobPoly_eq_map, map_coe_map_intCastRingHom, ← frobPoly_eq_map,
          frobPolyFam_apply]

theorem map_nsmulFam (f : R →+* S) (n k : ℕ) :
    MvPowerSeries.map f (nsmulFam p R n k) = nsmulFam p S n k :=
  map_coe_map_intCastRingHom f _

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S}

theorem baseChangeEq_verschiebungInt [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) :
    baseChangeEq f h (verschiebungInt m) = verschiebungInt (baseChangeEq f h m) :=
  baseChangeEq_precomp f h isEndo_frobPolyFam isEndo_frobPolyFam (map_frobPolyFam f) m

theorem baseChangeEq_verschiebungInt_iterate [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (n : ℕ) (m : CartierModule p Φ) :
    baseChangeEq f h ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] m) =
      (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[n] (baseChangeEq f h m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw
        [Function.iterate_succ_apply, Function.iterate_succ_apply, ← baseChangeEq_verschiebungInt,
            ih]

theorem baseChangeEq_vExpansion [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {ι : Type*} [Fintype ι] (N : ℕ) (c : Fin N → ι → R) (e : ι → CartierModule p Φ)
    (r : CartierModule p Φ) :
    baseChangeEq f h ((∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (∑ i, homothety (c m i) (e i))) + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] r) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m]
        (∑ i, homothety (f (c m i)) (baseChangeEq f h (e i)))) +
        (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] (baseChangeEq f h r) := by
  rw [(baseChangeEq (p := p) f h).map_add, map_sum (baseChangeEq (p := p) f h) _ Finset.univ,
    baseChangeEq_verschiebungInt_iterate]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebungInt_iterate, map_sum (baseChangeEq (p := p) f h) _ Finset.univ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact baseChangeEq_homothety f h _ _

theorem baseChangeEq_vExpansion_charP [Φ.IsComm] [Ψ.IsComm] [CharP R p] [CharP S p] (f : R →+* S)
    (h : Φ.map f = Ψ) {ι : Type*} [Fintype ι] (N : ℕ) (c : Fin N → ι → R)
    (e : ι → CartierModule p Φ) (r : CartierModule p Φ) :
    baseChangeEq f h ((∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m]
        (∑ i, homothety (c m i) (e i))) + (⇑(verschiebung (p := p) (Φ := Φ)))^[N] r) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Ψ)))^[m]
        (∑ i, homothety (f (c m i)) (baseChangeEq f h (e i)))) +
        (⇑(verschiebung (p := p) (Φ := Ψ)))^[N] (baseChangeEq f h r) := by
  rw [(baseChangeEq (p := p) f h).map_add, map_sum (baseChangeEq (p := p) f h) _ Finset.univ,
    baseChangeEq_verschiebung_iterate]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebung_iterate, map_sum (baseChangeEq (p := p) f h) _ Finset.univ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact baseChangeEq_homothety f h _ _

theorem det_tangent_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι ≃ Fin d) (e : ι → CartierModule p Φ) :
    (Matrix.of fun i i' => tangent (baseChangeEq f h (e i)) (σ i')).det =
      f (Matrix.of fun i i' => tangent (e i) (σ i')).det := by
  have hM : (Matrix.of fun i i' => tangent (baseChangeEq f h (e i)) (σ i')) =
      f.mapMatrix (Matrix.of fun i i' => tangent (e i) (σ i')) := by
    ext i i'
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, tangent_baseChangeEq]
  rw [hM, ← RingHom.map_det]

theorem isUnit_det_tangent_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (e : Fin d → CartierModule p Φ) (he : IsUnit (Matrix.of fun i j => tangent (e i) j).det) :
    IsUnit (Matrix.of fun i j => tangent (baseChangeEq f h (e i)) j).det := by
  have h1 := det_tangent_baseChangeEq f h (Equiv.refl (Fin d)) e
  simp only [Equiv.refl_apply] at h1
  rw [h1]
  exact he.map f

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule SpecialFormal

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

theorem actEnd_map_toPowerSeries (φ : B →+* B') (X : FormalODModule p B) (a : Zp2 p) (i : Fin 2) :
    ((X.map φ).actEnd a).toPowerSeries i = MvPowerSeries.map φ ((X.actEnd a).toPowerSeries i) :=
  rfl

theorem varpiEnd_map_toPowerSeries (φ : B →+* B') (X : FormalODModule p B) (i : Fin 2) :
    ((X.map φ).varpiEnd).toPowerSeries i = MvPowerSeries.map φ (X.varpiEnd.toPowerSeries i) :=
  rfl

theorem baseChange_endAct_actEnd (φ : B →+* B') (X : FormalODModule p B) (a : Zp2 p)
    (f : CartierModule p X.F) :
    baseChange φ (endAct (X.actEnd a) f) = endAct ((X.map φ).actEnd a) (baseChange φ f) :=
  baseChangeEq_endAct φ rfl (actEnd_map_toPowerSeries φ X a) f

theorem baseChange_endAct_varpiEnd (φ : B →+* B') (X : FormalODModule p B)
    (f : CartierModule p X.F) :
    baseChange φ (endAct X.varpiEnd f) = endAct (X.map φ).varpiEnd (baseChange φ f) :=
  baseChangeEq_endAct φ rfl (varpiEnd_map_toPowerSeries φ X) f

theorem baseChange_mem_gradedPiece (φ : B →+* B') (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    baseChange φ f ∈ (X.map φ).gradedPiece (φ.comp j) n := by
  intro c
  rw [← baseChange_endAct_actEnd, hf c, baseChangeEq_homothety, RingHom.comp_apply, map_pow]
  rfl

/-- **Homogeneous `V`-basis of the Cartier module.** For a formal `O_D`-module `X` over `B` and
`j : Zp2 p →+* B`, a pair `γ` of elements of the Cartier module of `X` with `γ i` in the graded
piece `i` (`X.gradedPiece j i`) for `i = 0, 1`, such that the matrix `(tangent (γ i) k)` of their
tangent vectors has unit determinant. Unlike `GradedCartierModuleData.IsHomogeneousVBasis`, it
does not ask that every element be `∑ [b i] • γ i + V y` for exactly one `b` and `y`. -/
def IsHomogeneousVBasis (X : FormalODModule p B) (j : Zp2 p →+* B)
    (γ : Fin 2 → CartierModule p X.F) :
    Prop :=
  (∀ i : Fin 2, γ i ∈ X.gradedPiece j i) ∧ IsUnit (Matrix.of fun i k => tangent (γ i) k).det

theorem IsHomogeneousVBasis.map (φ : B →+* B') {X : FormalODModule p B} {j : Zp2 p →+* B}
    {γ : Fin 2 → CartierModule p X.F} (h : X.IsHomogeneousVBasis j γ) :
    (X.map φ).IsHomogeneousVBasis (φ.comp j) fun i => baseChange φ (γ i) :=
  ⟨fun i => baseChange_mem_gradedPiece φ X j i (h.1 i), isUnit_det_tangent_baseChangeEq φ rfl γ h.2⟩

/-- **Structure constants of `ϖ` on the Cartier module.** For a formal `O_D`-module `X` over `B`,
`γ : Fin 2 → M` in the Cartier module `M` of `X` and `a : ℕ → Fin 2 → B`: for every `i` and every
`N`, `ϖ (γ i) = ∑_{m < N} V^m (homothety (a m i) (γ (piIndex m i))) + V^N h` for some `h`, where
`ϖ` acts by `endAct X.varpiEnd`, `V` is `verschiebungInt` and `piIndex` is
`GradedCartierModuleData.piIndex`. This is the expansion of
`GradedCartierModuleData.HasStructureConstants`, with `homothety (a m i)` for the action of the
Teichmüller representative `[a m i]`, stated on the Cartier module, so it needs no complementary
graded pieces. -/
def HasStructureConstants (X : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p X.F,
    endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (GradedCartierModuleData.piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] h

theorem HasStructureConstants.exists_eq {X : FormalODModule p B} {γ : Fin 2 → CartierModule p X.F}
    {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a) (i : Fin 2) (N : ℕ) :
    ∃ r : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (GradedCartierModuleData.piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] r :=
  h i N

theorem hasStructureConstants_order_zero (X : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin 0, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (GradedCartierModuleData.piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[0] h :=
  ⟨endAct X.varpiEnd (γ i), by simp⟩

theorem HasStructureConstants.map (φ : B →+* B') {X : FormalODModule p B}
    {γ : Fin 2 → CartierModule p X.F} {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a) :
    (X.map φ).HasStructureConstants (fun i => baseChange φ (γ i)) fun m i => φ (a m i) := by
  intro i N
  obtain ⟨r, hr⟩ := h i N
  refine ⟨baseChange φ r, ?_⟩
  have key := congrArg (baseChange (p := p) (Φ := X.F) φ) hr
  rw [baseChange_endAct_varpiEnd, (baseChange (p := p) (Φ := X.F) φ).map_add,
    map_sum
        (baseChange (p := p)
            (Φ := X.F) φ) _ Finset.univ, baseChangeEq_verschiebungInt_iterate] at key
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebungInt_iterate, baseChangeEq_homothety]
  rfl

theorem HasStructureConstants.exists_eq_verschiebung [CharP B p] {X : FormalODModule p B}
    {γ : Fin 2 → CartierModule p X.F} {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a)
    (i : Fin 2) (N : ℕ) :
    ∃ r : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (GradedCartierModuleData.piIndex m i)))) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] r := by
  obtain ⟨r, hr⟩ := h i N
  refine ⟨r, ?_⟩
  rw [hr, verschiebungInt_eq_verschiebung]

end FormalODModule

end CerednikDrinfeld

end
