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
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_LatticeTreeOrbital.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd

/-!
# Vertices of the lattice graph

For a commutative ring `R` and any `R`-algebra field `K`, `LT.LatticeTree.Vertex R K` is the type
of homothety classes of full `R`-lattices in `K²`, with the induced action of `GL₂(K)`. Adjacency
(`LT.LatticeTree.AdjacentLattice`), and with it the graph `CerednikDrinfeld.BruhatTits.tree` on
these classes, needs `K` to be the fraction field of `R`; when `R` is moreover a discrete valuation
ring, that graph is the Bruhat-Tits tree of `PGL₂(K)`. When `K` is the fraction field of `R`, the
stabilizer of the standard vertex is `Kˣ · GL₂(R)`, and for an irreducible `ϖ` the lattices `R²`
and `diag(1, ϖ) R²` are adjacent, as are `diag(1, ϖ) R²` and `diag(1, ϖ)² R²`, and neither
`diag(1, ϖ)` nor `diag(1, ϖ)²` fixes the standard vertex.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace LT.LatticeTree

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in
/-- Homothety of full lattices, `L ~ c • L` for `c ∈ Kˣ`, as a setoid. -/
def homothetySetoid : Setoid (FullLattice R K) where
  r L L' := Homothetic L.1 L'.1
  iseqv := ⟨fun L => Homothetic.refl L.1, Homothetic.symm, Homothetic.trans⟩

variable (R K) in
/-- The homothety classes of full `R`-lattices in `K²`, for any `R`-algebra field `K`. When `K` is
the fraction field of `R`, they are the vertices of the graph `CerednikDrinfeld.BruhatTits.tree`.
-/
def Vertex : Type _ := Quotient (homothetySetoid R K)

variable (R K) in
/-- The vertex of a full lattice. -/
def Vertex.mk (L : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L) : Vertex R K :=
  Quotient.mk (homothetySetoid R K) ⟨L, hL⟩

variable (R K) in
/-- The standard vertex, the class of the standard lattice `R²`. -/
def stdVertex : Vertex R K := Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice

theorem Vertex.mk_eq_mk_iff {L L' : Submodule R (Fin 2 → K)} {hL : Submodule.IsFullLattice K L}
    {hL' : Submodule.IsFullLattice K L'} :
    Vertex.mk R K L hL = Vertex.mk R K L' hL' ↔ Homothetic L L' :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- The action of `GL₂(K)` on vertices, induced by `L ↦ g L`. -/
def Vertex.act (g : Matrix.GeneralLinearGroup (Fin 2) K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeMap g L.1, IsFullLattice.map L.2 g⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      exact ⟨c, by
        change latticeMap (scalarGL c) (latticeMap g L) = latticeMap g L'
        rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, hc]⟩)

@[simp] theorem Vertex.act_mk (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L) :
    Vertex.act g (Vertex.mk R K L hL) = Vertex.mk R K (latticeMap g L) (IsFullLattice.map hL g) :=
  rfl

theorem Vertex.act_one (v : Vertex R K) : Vertex.act 1 v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_one L.1))

theorem Vertex.act_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act (g * h) v = Vertex.act g (Vertex.act h v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_mul g h L.1))

/-- A submodule homothetic to `R²`, contained in `R²`, and containing a vector with first coordinate
`1` is `R²`. -/
theorem eq_stdLattice_of_homothetic_of_le {L : Submodule R (Fin 2 → K)}
    (hhom : Homothetic (stdLattice R K) L) (hle : L ≤ stdLattice R K)
    {v : Fin 2 → K} (hv : v ∈ L) (hv0 : v 0 = 1) : L = stdLattice R K := by
  obtain ⟨c, rfl⟩ := hhom
  have hc : IsLocalization.IsInteger R ((c : K)) := by
    have h1 : (c : K) • (Pi.single 0 1 : Fin 2 → K) ∈
        latticeMap (scalarGL c) (stdLattice R K) :=
      mem_latticeMap_scalarGL.mpr ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, rfl⟩
    have h2 := hle h1 0
    rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
  have hcw : (c : K) * w 0 = 1 := by
    have h3 := congrFun hwv 0
    rw [Pi.smul_apply, smul_eq_mul] at h3
    rw [h3, hv0]
  have hcinv : IsLocalization.IsInteger R (((c⁻¹ : Kˣ) : K)) := by
    have h4 : ((c⁻¹ : Kˣ) : K) = w 0 := by
      calc ((c⁻¹ : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) * ((c : K) * w 0) := by rw [hcw, mul_one]
        _ = (((c⁻¹ : Kˣ) : K) * (c : K)) * w 0 := by rw [mul_assoc]
        _ = w 0 := by rw [Units.inv_mul, one_mul]
    rw [h4]
    exact hw 0
  apply le_antisymm hle
  intro u hu
  rw [mem_latticeMap_scalarGL]
  refine ⟨((c⁻¹ : Kˣ) : K) • u, fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul]
    exact IsLocalization.isInteger_mul hcinv (hu i)
  · rw [smul_smul, Units.mul_inv, one_smul]

variable [IsFractionRing R K]

/-- When `K` is the fraction field of `R`, the stabilizer of the standard vertex is `Kˣ · GL₂(R)`.
-/
theorem Vertex.act_stdVertex_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.act g (stdVertex R K) = stdVertex R K ↔
      ∃ c : Kˣ, scalarGL c * g ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (latticeMap_stdLattice_eq_iff_mem_range _).mp (by
      rw [latticeMap_mul]
      exact hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by
      rw [← latticeMap_mul]
      exact (latticeMap_stdLattice_eq_iff_mem_range _).mpr hc⟩

theorem single_one_one_notMem_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    (Pi.single 1 1 : Fin 2 → K) ∉
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  rintro ⟨-, w, hw, hweq⟩
  rw [unitOfNeZero_coe, Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

theorem latticeMap_diagSnd_ne_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      stdLattice R K := fun h =>
  single_one_one_notMem_latticeMap_diagSnd hϖ (h ▸ single_one_mem_stdLattice R K 1)

theorem latticeMap_diagSnd_le_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ stdLattice R K := by
  intro v hv
  rw [mem_latticeMap_diagSnd_stdLattice] at hv
  obtain ⟨h0, w, hw, hw'⟩ := hv
  intro i
  fin_cases i
  · exact h0
  · change IsLocalization.IsInteger R (v 1)
    rw [← hw', unitOfNeZero_coe]
    exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw

theorem latticeMap_diagSnd_lt_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K :=
  lt_of_le_of_ne (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
    (latticeMap_diagSnd_ne_stdLattice hϖ)

theorem not_homothetic_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
  intro hhom
  exact latticeMap_diagSnd_ne_stdLattice hϖ
    (eq_stdLattice_of_homothetic_of_le hhom (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
      (single_zero_one_mem_latticeMap_diagSnd _) (Pi.single_eq_same 0 1))

/-- When `K` is the fraction field of `R` and `ϖ` is irreducible, `diag(1, ϖ)` moves the standard
vertex. -/
theorem stdVertex_ne_act_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd hϖ h.symm

/-- For `K` the fraction field of `R`, adjacency of `R`-submodules of `K²`: `ϖ L < L' < L` for some
irreducible `ϖ`. -/
def AdjacentLattice (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) L < L' ∧ L' < L

theorem mem_latticeMap_scalarGL_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ↔
      ∀ i, ∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K ϖ * w = v i := by
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    exact ⟨w i, hw i, by rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]⟩
  · intro h
    choose w hw hw' using h
    refine ⟨w, hw, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]
    exact hw' i

theorem latticeMap_scalarGL_le_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at hv
  rw [mem_latticeMap_diagSnd_stdLattice]
  obtain ⟨w0, hw0, hw0'⟩ := hv 0
  obtain ⟨w1, hw1, hw1'⟩ := hv 1
  refine ⟨?_, w1, hw1, by rw [unitOfNeZero_coe]; exact hw1'⟩
  rw [← hw0']
  exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw0

theorem latticeMap_scalarGL_ne_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro h
  have he0 := single_zero_one_mem_latticeMap_diagSnd
    (R := R) (unitOfNeZero (K := K) hϖ.ne_zero)
  rw [← h, mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at he0
  obtain ⟨w, hw, hweq⟩ := he0 0
  rw [Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

/-- When `K` is the fraction field of `R` and `ϖ` is irreducible, the lattices `R²` and
`diag(1, ϖ) R²` are adjacent. -/
theorem adjacentLattice_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) :=
  ⟨ϖ, hϖ,
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ),
    latticeMap_diagSnd_lt_stdLattice hϖ⟩

theorem adjacentLattice_diagSnd_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  have h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) :=
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ)
  have h₂ : latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K := latticeMap_diagSnd_lt_stdLattice hϖ
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff _).mpr h₂⟩
  have h₃ := (latticeMap_lt_latticeMap_iff
    (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))).mpr h₁
  rwa [← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul] at h₃

theorem latticeMap_diagSnd_sq_le_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) ≤
      stdLattice R K :=
  le_trans (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero))
    (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)

theorem not_homothetic_stdLattice_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  intro hhom
  have he0 : (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    have h5 := mulVec_mem_latticeMap (g := diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
      (single_zero_one_mem_latticeMap_diagSnd (R := R)
        (unitOfNeZero (K := K) hϖ.ne_zero))
    have h6 : ((diagSnd (unitOfNeZero (K := K) hϖ.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single 0 1 : Fin 2 → K) = (Pi.single 0 1 : Fin 2 → K) := by
      rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp
    rwa [h6] at h5
  have heq := eq_stdLattice_of_homothetic_of_le hhom
    (latticeMap_diagSnd_sq_le_stdLattice hϖ) he0 (Pi.single_eq_same 0 1)
  have he1 : (Pi.single 1 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    rw [heq]
    exact single_one_mem_stdLattice R K 1
  exact single_one_one_notMem_latticeMap_diagSnd hϖ
    (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero) he1)

/-- When `K` is the fraction field of `R` and `ϖ` is irreducible, `diag(1, ϖ)²` moves the standard
vertex. -/
theorem stdVertex_ne_act_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K)) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd_sq hϖ h.symm

end LT.LatticeTree

end
