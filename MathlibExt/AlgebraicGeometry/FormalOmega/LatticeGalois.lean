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

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeVertex

/-!
# Integral automorphisms acting on lattices and vertices

An `LT.LatticeTree.IntegralAut R K` is a ring automorphism of `K` with a compatible automorphism of
`R`. It acts coordinatewise on `K²`, on `R`-submodules of `K²` (`LT.LatticeTree.latticeGal`), on
full lattices and on vertices. For `δ ∈ GL₂(K)` and any integral automorphism `σ`,
`LT.LatticeTree.normTwo δ σ` and `LT.LatticeTree.normThree δ σ` are the products `δ σ(δ)` and
`δ σ(δ) σ²(δ)`. If `σ² = id`, applying the twisted action `L ↦ δ σ(L)` twice is the action of
`δ σ(δ)`; if `σ³ = id`, applying it three times is the action of `δ σ(δ) σ²(δ)`.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

/-- A ring automorphism of `K` together with a compatible ring automorphism of `R`, so that it
preserves the `R`-integral elements of `K`. -/
structure IntegralAut (R K : Type*) [CommRing R] [Field K] [Algebra R K] where
  /-- The automorphism of the field `K`. -/
  toField : K ≃+* K
  /-- The automorphism of the base ring `R`. -/
  toBase : R ≃+* R
  /-- The two automorphisms are compatible with the algebra map. -/
  commutes : ∀ r : R, toField (algebraMap R K r) = algebraMap R K (toBase r)

namespace IntegralAut

variable (R K) in
/-- The identity integral automorphism. -/
def refl : IntegralAut R K where
  toField := RingEquiv.refl K
  toBase := RingEquiv.refl R
  commutes _ := rfl

@[simp] theorem refl_toField : (refl R K).toField = RingEquiv.refl K := rfl

@[simp] theorem refl_toBase : (refl R K).toBase = RingEquiv.refl R := rfl

/-- Composition of integral automorphisms, `(σ.comp τ) x = σ (τ x)`. -/
def comp (σ τ : IntegralAut R K) : IntegralAut R K where
  toField := τ.toField.trans σ.toField
  toBase := τ.toBase.trans σ.toBase
  commutes r := by
    change σ.toField (τ.toField (algebraMap R K r)) = algebraMap R K (σ.toBase (τ.toBase r))
    rw [τ.commutes, σ.commutes]

@[simp] theorem comp_toField_apply (σ τ : IntegralAut R K) (x : K) :
    (σ.comp τ).toField x = σ.toField (τ.toField x) := rfl

@[simp] theorem comp_toBase_apply (σ τ : IntegralAut R K) (r : R) :
    (σ.comp τ).toBase r = σ.toBase (τ.toBase r) := rfl

theorem symm_commutes (σ : IntegralAut R K) (r : R) :
    σ.toField.symm (algebraMap R K r) = algebraMap R K (σ.toBase.symm r) := by
  apply σ.toField.injective
  rw [RingEquiv.apply_symm_apply, σ.commutes, RingEquiv.apply_symm_apply]

/-- The inverse integral automorphism. -/
def symm (σ : IntegralAut R K) : IntegralAut R K where
  toField := σ.toField.symm
  toBase := σ.toBase.symm
  commutes := σ.symm_commutes

theorem symm_toField (σ : IntegralAut R K) : σ.symm.toField = σ.toField.symm := rfl

attribute [local simp] symm_toField
theorem symm_toBase (σ : IntegralAut R K) : σ.symm.toBase = σ.toBase.symm := rfl

attribute [local simp] symm_toBase
theorem isInteger_map (σ : IntegralAut R K) {x : K}
    (hx : IsLocalization.IsInteger R x) : IsLocalization.IsInteger R (σ.toField x) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨σ.toBase r, (σ.commutes r).symm⟩

/-- The induced automorphism of `GL₂(K)`, applying `σ` entrywise. -/
def mapGL (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)

theorem mapGL_apply (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (i j : Fin 2) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      σ.toField ((g : Matrix (Fin 2) (Fin 2) K) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

theorem mapGL_coe (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g : Matrix (Fin 2) (Fin 2) K)).map (σ.toField : K →+* K) := by
  ext i j
  rw [mapGL_apply, Matrix.map_apply]
  rfl

theorem mapGL_comp (σ τ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (σ.comp τ).mapGL g = σ.mapGL (τ.mapGL g) := by
  ext i j
  rw [mapGL_apply, mapGL_apply, mapGL_apply, comp_toField_apply]

theorem mapGL_refl (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (refl R K).mapGL g = g := by
  ext i j
  rw [mapGL_apply]
  rfl

/-- The induced automorphism of `Kˣ`. -/
def unitMap (σ : IntegralAut R K) (c : Kˣ) : Kˣ where
  val := σ.toField c
  inv := σ.toField ↑c⁻¹
  val_inv := by rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by rw [← map_mul, Units.inv_mul, map_one]

@[simp] theorem unitMap_coe (σ : IntegralAut R K) (c : Kˣ) :
    ((σ.unitMap c : Kˣ) : K) = σ.toField c := rfl

end IntegralAut

attribute [local simp] IntegralAut.symm_toField IntegralAut.symm_toBase

/-- The coordinatewise action of an integral automorphism on `K²`. -/
def galVec (σ : IntegralAut R K) (v : Fin 2 → K) : Fin 2 → K :=
  fun i => σ.toField (v i)

@[simp] theorem galVec_apply (σ : IntegralAut R K) (v : Fin 2 → K) (i : Fin 2) :
    galVec σ v i = σ.toField (v i) := rfl

theorem galVec_add (σ : IntegralAut R K) (v w : Fin 2 → K) :
    galVec σ (v + w) = galVec σ v + galVec σ w := by
  funext i
  simp [galVec, map_add]

theorem galVec_zero (σ : IntegralAut R K) : galVec σ (0 : Fin 2 → K) = 0 := by
  funext i
  simp [galVec]

theorem galVec_smul (σ : IntegralAut R K) (r : R) (v : Fin 2 → K) :
    galVec σ (r • v) = σ.toBase r • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, Algebra.smul_def,
    Algebra.smul_def, map_mul, σ.commutes]

theorem galVec_smul_field (σ : IntegralAut R K) (c : K) (v : Fin 2 → K) :
    galVec σ (c • v) = σ.toField c • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, smul_eq_mul, smul_eq_mul,
    map_mul]

theorem galVec_galVec (σ τ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec τ v) = galVec (σ.comp τ) v := rfl

@[simp] theorem galVec_refl (v : Fin 2 → K) : galVec (IntegralAut.refl R K) v = v := rfl

theorem galVec_symm_galVec (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ.symm (galVec σ v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_symm_galVec
theorem galVec_galVec_symm (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec σ.symm v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_galVec_symm
theorem galVec_mulVec (σ : IntegralAut R K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) :
    galVec σ (M *ᵥ v) = (M.map (σ.toField : K →+* K)) *ᵥ galVec σ v := by
  funext i
  rw [galVec_apply]
  exact RingHom.map_mulVec (σ.toField : K →+* K) M v i

/-- The image of an `R`-submodule of `K²` under `galVec σ`. -/
def latticeGal (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) where
  carrier := galVec σ '' L
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, L.add_mem hv hw, galVec_add σ v w⟩
  zero_mem' := ⟨0, L.zero_mem, galVec_zero σ⟩
  smul_mem' := by
    rintro r _ ⟨w, hw, rfl⟩
    refine ⟨σ.toBase.symm r • w, L.smul_mem _ hw, ?_⟩
    rw [galVec_smul, RingEquiv.apply_symm_apply]

theorem mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {v : Fin 2 → K} : v ∈ latticeGal σ L ↔ ∃ w ∈ L, galVec σ w = v := Iff.rfl

theorem galVec_mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {w : Fin 2 → K} (hw : w ∈ L) : galVec σ w ∈ latticeGal σ L :=
  ⟨w, hw, rfl⟩

@[simp] theorem latticeGal_refl (L : Submodule R (Fin 2 → K)) :
    latticeGal (IntegralAut.refl R K) L = L := by
  ext v
  exact ⟨fun ⟨w, hw, h⟩ => h ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

theorem latticeGal_comp (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    latticeGal (σ.comp τ) L = latticeGal σ (latticeGal τ L) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨galVec τ w, galVec_mem_latticeGal hw, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem latticeGal_symm_latticeGal (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ.symm (latticeGal σ L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_symm_galVec]
  · intro hv
    exact ⟨galVec σ v, galVec_mem_latticeGal hv, galVec_symm_galVec σ v⟩

attribute [local simp] latticeGal_symm_latticeGal
theorem latticeGal_latticeGal_symm (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ (latticeGal σ.symm L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_galVec_symm]
  · intro hv
    exact ⟨galVec σ.symm v, galVec_mem_latticeGal hv, galVec_galVec_symm σ v⟩

attribute [local simp] latticeGal_latticeGal_symm
theorem latticeGal_injective (σ : IntegralAut R K) :
    Function.Injective (latticeGal (R := R) (K := K) σ) :=
  Function.LeftInverse.injective (latticeGal_symm_latticeGal σ)

theorem latticeGal_span (σ : IntegralAut R K) (s : Set (Fin 2 → K)) :
    latticeGal σ (Submodule.span R s) = Submodule.span R (galVec σ '' s) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [galVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [galVec_smul]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact galVec_mem_latticeGal (Submodule.subset_span hx)

theorem latticeGal_stdLattice (σ : IntegralAut R K) :
    latticeGal σ (stdLattice R K) = stdLattice R K := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    intro i
    exact σ.isInteger_map (hw i)
  · intro v hv
    refine ⟨galVec σ.symm v, fun i => ?_, galVec_galVec_symm σ v⟩
    exact σ.symm.isInteger_map (hv i)

theorem latticeGal_latticeMap (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap g L) = latticeMap (σ.mapGL g) (latticeGal σ L) := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨galVec σ w, galVec_mem_latticeGal hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]

theorem latticeGal_latticeMap_stdLattice (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeGal σ (latticeMap g (stdLattice R K)) =
      latticeMap (σ.mapGL g) (stdLattice R K) := by
  rw [latticeGal_latticeMap, latticeGal_stdLattice]

theorem mapGL_scalarGL (σ : IntegralAut R K) (c : Kˣ) :
    σ.mapGL (scalarGL c) = scalarGL (σ.unitMap c) := by
  ext i j
  rw [σ.mapGL_apply, scalarGL_coe, scalarGL_coe, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, IntegralAut.unitMap_coe]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, map_zero]

theorem latticeGal_scalarGL (σ : IntegralAut R K) (c : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap (scalarGL c) L) =
      latticeMap (scalarGL (σ.unitMap c)) (latticeGal σ L) := by
  rw [latticeGal_latticeMap, mapGL_scalarGL]

/-- `galVec σ` maps full lattices to full lattices. -/
theorem IsFullLattice.gal {L : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L)
    (σ : IntegralAut R K) : Submodule.IsFullLattice K (latticeGal σ L) where
  fg := by
    obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Submodule.IsLattice.fg K L)
    exact Submodule.fg_def.mpr
      ⟨galVec σ '' S, hSfin.image _, by rw [← latticeGal_span, hS]⟩
  linearIndepOn s hs hli := by
    have hinj : ∀ τ : IntegralAut R K, Function.Injective (galVec τ) := fun τ v w h => by
      rw [← galVec_symm_galVec τ v, h, galVec_symm_galVec]
    have hsurj : ∀ τ : IntegralAut R K, Function.Surjective (galVec τ) := fun τ v =>
      ⟨galVec τ.symm v, galVec_galVec_symm τ v⟩
    let j : IntegralAut R K → (Fin 2 → K) →+ (Fin 2 → K) := fun τ =>
      { toFun := galVec τ, map_zero' := galVec_zero τ, map_add' := galVec_add τ }
    have ht : LinearIndepOn R id (galVec σ.symm '' s) := by
      have h := LinearIndependent.map_of_surjective_injectiveₛ hli σ.symm.toBase (j σ.symm)
        σ.symm.toBase.surjective (hinj σ.symm) fun r m => galVec_smul σ.symm r m
      exact (linearIndepOn_iff_image (hinj σ.symm).injOn).mp h
    have htL : galVec σ.symm '' s ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hs hv
      rwa [galVec_symm_galVec]
    have hK := Submodule.IsLattice.linearIndepOn (A := K) _ htL ht
    have h := LinearIndependent.map_of_surjective_injectiveₛ hK σ.toField (j σ)
      σ.toField.surjective (hinj σ) fun c m => galVec_smul_field σ c m
    have h' := (linearIndepOn_iff_image (hinj σ).injOn).mp h
    rwa [Set.image_image, Set.image_congr fun v _ => galVec_galVec_symm σ v,
      Set.image_id'] at h'
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    have hv : galVec σ.symm v ∈ Submodule.span K (L : Set (Fin 2 → K)) :=
      hL.span_eq_top ▸ Submodule.mem_top
    have hkey : ∀ w ∈ Submodule.span K (L : Set (Fin 2 → K)),
        galVec σ w ∈ Submodule.span K ((latticeGal σ L : Set (Fin 2 → K))) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (galVec_mem_latticeGal hx)
      | zero => rw [galVec_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [galVec_smul_field]; exact Submodule.smul_mem _ _ hx
    have := hkey _ hv
    rwa [galVec_galVec_symm] at this

/-- The action of an integral automorphism on vertices. -/
def Vertex.galAct (σ : IntegralAut R K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeGal σ L.1, IsFullLattice.gal L.2 σ⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨σ.unitMap c, ?_⟩
      change latticeMap _ (latticeGal σ L) = latticeGal σ L'
      rw [← latticeGal_scalarGL, hc])

@[simp] theorem Vertex.galAct_mk (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K))
    (hL : Submodule.IsFullLattice K L) :
    Vertex.galAct σ (Vertex.mk R K L hL) =
      Vertex.mk R K (latticeGal σ L) (IsFullLattice.gal hL σ) :=
  rfl

theorem Vertex.galAct_stdVertex (σ : IntegralAut R K) :
    Vertex.galAct σ (stdVertex R K) = stdVertex R K := by
  rw [stdVertex, Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_stdLattice]
  exact Homothetic.refl _

/-- The twisted action `L ↦ δ σ(L)` on `R`-submodules of `K²`. -/
def twistedLatticeMap (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  latticeMap δ (latticeGal σ L)

/-- The twisted action maps full lattices to full lattices. -/
theorem IsFullLattice.twisted {L : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Submodule.IsFullLattice K (twistedLatticeMap δ σ L) :=
  IsFullLattice.map (IsFullLattice.gal hL σ) δ

theorem twistedLatticeMap_twistedLatticeMap (δ δ' : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ' τ L) =
      twistedLatticeMap (δ * σ.mapGL δ') (σ.comp τ) L := by
  unfold twistedLatticeMap
  rw [latticeGal_latticeMap, ← latticeMap_mul, latticeGal_comp]

/-- The product `δ σ(δ)`, for any integral automorphism `σ`. -/
def normTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ

/-- The product `δ σ(δ) σ²(δ)`, for any integral automorphism `σ`. -/
def normThree (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ * (σ.comp σ).mapGL δ

/-- If `σ² = id`, applying the twisted action twice is the action of `normTwo δ σ`. -/
theorem twistedLatticeMap_two_of_orderTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : σ.comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ L) = latticeMap (normTwo δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normTwo
  rw [latticeGal_refl]

/-- If `σ³ = id`, applying the twisted action three times is the action of `normThree δ σ`. -/
theorem twistedLatticeMap_three_of_orderThree (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ (twistedLatticeMap δ σ L)) =
      latticeMap (normThree δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normThree
  rw [latticeGal_refl]

theorem latticeMap_norm_eq_self_of_twisted_fixed (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    {L : Submodule R (Fin 2 → K)} (hL : twistedLatticeMap δ σ L = L) :
    latticeMap (normThree δ σ) L = L := by
  rw [← twistedLatticeMap_three_of_orderThree δ hσ, hL, hL, hL]

end LT.LatticeTree

end
