/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean`,
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal`
`CF_DeligneDatum_edgeNondegAt_of_vertexNondegAt`
`CF_DeligneDatum_edgeNondegAt_pullback_act_inv`
`CF_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing`
`CF_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite`
`CF_DeligneDatum_inEdgeChart_act_of_isPullback`
`CF_DeligneDatum_inEdgeChart_swap`
`CF_DeligneDatum_inEdgeChart_act_scalarGL_iff`
`CF_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent`
`CF_DeligneDatum_vertexNondegAt_act_scalarGL_iff`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeEdge

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

/-- Edge nondegeneracy at the maximal ideal of a local ring gives membership in the edge chart. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) M' M) :
    d.InEdgeChart π M' M := by
  intro 𝔭 h𝔭
  have hsub : 𝔭 ≤ IsLocalRing.maximalIdeal B := IsLocalRing.le_maximalIdeal h𝔭.ne_top
  obtain ⟨hle, hπ, h1, h2⟩ := h
  refine ⟨hle, hπ, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · exact (sup_le_sup_left (Submodule.smul_mono_left hsub) (d.line M) :
      d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) ≤ _) hmem
  · exact (sup_le_sup_left (Submodule.smul_mono_left hsub) (d.line M') :
      d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) ≤ _) hmem

/-- Vertex nondegeneracy at `M` gives edge nondegeneracy at any edge `π M ⊆ M' ⊆ M`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_of_vertexNondegAt
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K)
    (hle : M'.1 ≤ M.1) (hπM : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1)
    (hV : d.VertexNondegAt π 𝔭 M) :
    d.EdgeNondegAt π 𝔭 M' M := by
  refine ⟨hle, hπM, ?_, ?_⟩
  · intro v hv
    refine hV v ?_
    rintro ⟨w, hw⟩
    exact hv (hw ▸ hπM w)
  · intro v' hv' hmem
    have hpush : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] v') ∈
        d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      rw [← hyz, map_add]
      refine Submodule.mem_sup.mpr ⟨inclBaseChange B hle y,
        d.mono hle (Submodule.mem_map_of_mem hy), inclBaseChange B hle z, ?_, rfl⟩
      refine Submodule.smul_induction_on (p := fun z => inclBaseChange B hle z ∈
          (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) hz
        (fun r hr n _ => ?_) (fun x y hx hy => ?_)
      · rw [LinearMap.map_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · rw [LinearMap.map_add]
        exact Submodule.add_mem _ hx hy
    have hincl : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] v') =
        (1 : B) ⊗ₜ[𝒪] (⟨(v' : Fin 2 → K), hle v'.2⟩ : ↥M.1) := rfl
    rw [hincl] at hpush
    exact hV ⟨(v' : Fin 2 → K), hle v'.2⟩ hv' hpush

/-- Edge nondegeneracy at `N' ⊆ N` transfers to the pullback along `h` at `h⁻¹ N' ⊆ h⁻¹ N`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (h : Matrix.GeneralLinearGroup (Fin 2) K) (𝔭 : Ideal B)
    (N' N : FullLattice 𝒪 K)
    (hN : d.EdgeNondegAt π 𝔭 N' N) :
    (DeligneDatum.pullback π B h d).EdgeNondegAt π 𝔭 (FullLattice.act h⁻¹ N')
      (FullLattice.act h⁻¹ N) := by
  obtain ⟨hle, hπ, h1, h2⟩ := hN
  refine ⟨latticeMap_mono h⁻¹ hle, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    rw [← hwv, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
  · intro v hv hmem
    refine h1 ⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
      (act_act_inv h N).le (mulVec_mem_latticeMap v.2)⟩
      ?_ (DeligneDatum.tmul_mulVec_mem π d h N 𝔭 v hmem)
    intro hgv
    apply hv
    have h' := mulVec_mem_latticeMap (g := h⁻¹) hgv
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h'
  · intro v' hv' hmem
    refine h2 ⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ (v' : Fin 2 → K),
      (act_act_inv h N').le (mulVec_mem_latticeMap v'.2)⟩
      ?_ (DeligneDatum.tmul_mulVec_mem π d h N' 𝔭 v' hmem)
    rintro ⟨w, hw⟩
    apply hv'
    refine ⟨⟨((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (w : Fin 2 → K), mulVec_mem_latticeMap w.2⟩, ?_⟩
    change (v' : Fin 2 → K) = algebraMap 𝒪 K π •
      (((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (w : Fin 2 → K))
    rw [← Matrix.mulVec_smul, ← hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]

/-- Over a local ring in which `π` is nilpotent, every Deligne datum is, up to a pullback along
some `h ∈ GL₂(K)`, in the edge chart of the standard edge `g 𝒪² ⊆ 𝒪²`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (d' : DeligneDatum (K := K) π B),
      DeligneDatum.IsPullback (K := K) (π := π) B h d d' ∧
      d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
  classical
  have h𝔪 : (IsLocalRing.maximalIdeal B).IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have hcoe : ((unitOfNeZero (K := K) hπ.ne_zero : Kˣ) : K) = algebraMap 𝒪 K π :=
    unitOfNeZero_coe hπ.ne_zero
  obtain ⟨P', P, hP₁, hP₂, hE⟩ : ∃ P' P : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) P.1 < P'.1 ∧ P'.1 < P.1 ∧
        d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) P' P := by
    obtain ⟨M', M, hMM⟩ := d.exists_edgeNondegAt π (IsLocalRing.maximalIdeal B) h𝔪
    have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hv
      rw [hcoe]
      exact hMM.2.1 ⟨w, hw⟩
    by_cases hdeg : M'.1 = M.1 ∨
        M'.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1
    · have hV : d.VertexNondegAt π (IsLocalRing.maximalIdeal B) M := by
        rcases hdeg with heq | heq
        · have hMM' : M' = M := Subtype.ext heq
          subst hMM'
          exact hMM.2.2.2
        · intro v hv
          refine hMM.2.2.1 v ?_
          rw [heq]
          intro hvmem
          obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.1 hvmem
          exact hv ⟨⟨w, hw⟩, by rw [← hwv, hcoe]⟩
      obtain ⟨M'', hlt₁, hlt₂⟩ := CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt π hπ M
      refine ⟨M'', M, hlt₁, hlt₂, ?_⟩
      refine DeligneDatum.edgeNondegAt_of_vertexNondegAt π d _ M'' M hlt₂.le ?_ hV
      intro v
      apply hlt₁.le
      rw [← hcoe]
      exact mem_latticeMap_scalarGL.2 ⟨v, v.2, rfl⟩
    · push Not at hdeg
      exact ⟨M', M, lt_of_le_of_ne hπle (Ne.symm hdeg.2), lt_of_le_of_ne hMM.1 hdeg.1, hMM⟩
  have hIn : d.InEdgeChart π P' P :=
    DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal π d P' P hE
  obtain ⟨h, hP, hP'⟩ :=
    CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ g
      hg P' P hP₁ hP₂
  refine ⟨h, DeligneDatum.pullback π B h d, DeligneDatum.isPullback_pullback π B h d, ?_⟩
  intro 𝔭 h𝔭
  have hT := DeligneDatum.edgeNondegAt_pullback_act_inv π d h 𝔭 P' P (hIn 𝔭 h𝔭)
  have e1 : FullLattice.act h⁻¹ P = stdFullLattice K := by
    rw [← hP]
    exact Subtype.ext (latticeMap_inv_latticeMap h _)
  have e2 : FullLattice.act h⁻¹ P' = FullLattice.act g (stdFullLattice K) := by
    rw [← hP']
    exact Subtype.ext (latticeMap_inv_latticeMap h _)
  rw [e1, e2] at hT
  exact hT

section FiniteCover

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem cov_rTensor_mem_sup {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) (𝔭' : Ideal B')
    (x : latticeBaseChange 𝒪 K B M)
    (hx : x ∈ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    LinearMap.rTensor (↥M.1) f.toLinearMap x ∈
      lineBaseChange f M N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  have aux : ∀ t ∈ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      LinearMap.rTensor (↥M.1) f.toLinearMap t ∈
        (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
    intro t ht
    induction ht using Submodule.smul_induction_on' with
    | smul a ha y _ =>
      rw [rTensor_smul_left]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    | add y _ z _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  obtain ⟨n, hn, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨n, hn, rfl⟩) (aux t ht)

private theorem cov_edgeNondegAt_of_map {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (D : DeligneDatum (K := K) π B) (𝔭' : Ideal B') (M' M : FullLattice 𝒪 K)
    (h : (DeligneDatum.map π f D).EdgeNondegAt π 𝔭' M' M) :
    D.EdgeNondegAt π (Ideal.comap f 𝔭') M' M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun v hv hmem => h3 v hv ?_, fun v' hv' hmem => h4 v' hv' ?_⟩
  · have := cov_rTensor_mem_sup f M (D.line M) 𝔭' _ hmem
    rwa [rTensor_one_tmul] at this
  · have := cov_rTensor_mem_sup f M' (D.line M') 𝔭' _ hmem
    rwa [rTensor_one_tmul] at this

omit [Algebra 𝒪 B] in
private theorem cov_isOpen_setOf_not_mem_sup {V : Type} [AddCommGroup V] [Module B V]
    (N : Submodule B V) [Module.Projective B (V ⧸ N)] (x : V) :
    IsOpen {𝔮 : PrimeSpectrum B | x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V)} := by
  have key : ∀ 𝔮 : PrimeSpectrum B, x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V) ↔
      ∃ φ : (V ⧸ N) →ₗ[B] B, φ (N.mkQ x) ∉ 𝔮.asIdeal := by
    intro 𝔮
    constructor
    · intro hx
      apply exists_linearMap_apply_not_mem
      intro hq
      apply hx
      have : x ∈ ((𝔮.asIdeal • ⊤ : Submodule B V).map N.mkQ).comap N.mkQ := by
        rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
        exact hq
      rwa [Submodule.comap_map_mkQ] at this
    · rintro ⟨φ, hφ⟩ hx
      apply hφ
      obtain ⟨n, hn, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
      have hn0 : N.mkQ n = 0 := by simpa using hn
      rw [map_add, hn0, zero_add]
      have ht' : N.mkQ t ∈ (𝔮.asIdeal • ⊤ : Submodule B (V ⧸ N)) := by
        rw [← Submodule.range_mkQ, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ht
      have := Submodule.mem_map_of_mem (f := φ) ht'
      rw [Submodule.map_smul''] at this
      have : φ (N.mkQ t) ∈ (𝔮.asIdeal • ⊤ : Submodule B B) :=
        Submodule.smul_mono le_rfl le_top this
      simpa [Ideal.mul_top] using this
  have : {𝔮 : PrimeSpectrum B | x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V)} =
      ⋃ φ : (V ⧸ N) →ₗ[B] B, (PrimeSpectrum.basicOpen (φ (N.mkQ x)) : Set (PrimeSpectrum B)) := by
    ext 𝔮
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, key]
    rfl
  rw [this]
  exact isOpen_iUnion fun φ => (PrimeSpectrum.basicOpen _).isOpen

private theorem cov_one_tmul_mem_of_mem_smul_top (L : FullLattice 𝒪 K) (𝔮 : Ideal B)
    (hπ𝔮 : algebraMap 𝒪 B π ∈ 𝔮) (t : ↥L.1)
    (ht : t ∈ (Ideal.span {π} • ⊤ : Submodule 𝒪 ↥L.1)) :
    (1 : B) ⊗ₜ[𝒪] t ∈ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
  induction ht using Submodule.smul_induction_on' with
  | smul a ha y _ =>
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      show (algebraMap 𝒪 B (c * π)) ⊗ₜ[𝒪] y = algebraMap 𝒪 B (c * π) • ((1 : B) ⊗ₜ[𝒪] y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [map_mul]
    exact 𝔮.mul_mem_left _ hπ𝔮
  | add y _ z _ hy hz =>
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hy hz

private theorem cov_isOpen_setOf_forall_not_mem [Finite (𝒪 ⧸ Ideal.span {π})]
    (hB : IsNilpotent (algebraMap 𝒪 B π))
    (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    [Module.Projective B (latticeBaseChange 𝒪 K B L ⧸ N)] (T : Set ↥L.1) :
    IsOpen {𝔮 : PrimeSpectrum B | ∀ v ∈ T,
      (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
  classical
  set I : Submodule 𝒪 ↥L.1 := (Ideal.span {π} : Ideal 𝒪) • ⊤ with hI
  have := L.2
  have : Module.Finite 𝒪 ↥L.1 := Submodule.IsLattice.finite K L.1
  have : Finite (↥L.1 ⧸ I) := Module.finite_of_finite (𝒪 ⧸ (Ideal.span {π} : Ideal 𝒪))
  have hπ𝔮 : ∀ 𝔮 : PrimeSpectrum B, algebraMap 𝒪 B π ∈ 𝔮.asIdeal := fun 𝔮 => by
    obtain ⟨n, hn⟩ := hB
    exact 𝔮.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have hinv : ∀ (𝔮 : PrimeSpectrum B) (v v' : ↥L.1), I.mkQ v = I.mkQ v' →
      ((1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ↔
       (1 : B) ⊗ₜ[𝒪] v' ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) := by
    intro 𝔮 v v' h
    have hvv' : v - v' ∈ I := (Submodule.Quotient.eq _).1 h
    have hmem := cov_one_tmul_mem_of_mem_smul_top π L 𝔮.asIdeal (hπ𝔮 𝔮) _ hvv'
    rw [TensorProduct.tmul_sub] at hmem
    constructor
    · intro hv hv'
      exact hv (by simpa using Submodule.add_mem _ (Submodule.mem_sup_right hmem) hv')
    · intro hv' hv
      exact hv' (by simpa using Submodule.sub_mem _ hv (Submodule.mem_sup_right hmem))
  have hrep : ∀ c ∈ I.mkQ '' T, ∃ v ∈ T, I.mkQ v = c := fun c hc => hc
  choose rep hrepT hrepmk using hrep
  have hfin : (I.mkQ '' T).Finite := Set.toFinite _
  have heq : {𝔮 : PrimeSpectrum B | ∀ v ∈ T,
      (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} =
      ⋂ c ∈ I.mkQ '' T, {𝔮 : PrimeSpectrum B | ∀ hc : c ∈ I.mkQ '' T,
        (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉
          N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
    ext 𝔮
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h c hc hc'
      exact h _ (hrepT c hc')
    · intro h v hv
      exact (hinv 𝔮 _ _ (hrepmk _ ⟨v, hv, rfl⟩)).1 (h _ ⟨v, hv, rfl⟩ ⟨v, hv, rfl⟩)
  rw [heq]
  refine hfin.isOpen_biInter fun c hc => ?_
  have : {𝔮 : PrimeSpectrum B | ∀ hc : c ∈ I.mkQ '' T, (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉
        N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} =
      {𝔮 : PrimeSpectrum B | (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉
        N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
    ext 𝔮
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => h hc, fun h _ => h⟩
  rw [this]
  exact cov_isOpen_setOf_not_mem_sup N _

private theorem cov_isOpen_setOf_edgeNondegAt [Finite (𝒪 ⧸ Ideal.span {π})]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (D : DeligneDatum (K := K) π B)
    (M' M : FullLattice 𝒪 K) :
    IsOpen {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} := by
  classical
  have := D.invertible M
  have := D.invertible M'
  by_cases hc : M'.1 ≤ M.1 ∧ (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1)
  · have heq : {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} =
        {𝔮 : PrimeSpectrum B | ∀ v ∈ {v : ↥M.1 | (v : Fin 2 → K) ∉ M'.1},
            (1 : B) ⊗ₜ[𝒪] v ∉
              D.line M ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))} ∩
        {𝔮 : PrimeSpectrum B | ∀ v' ∈ {v' : ↥M'.1 |
            ¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)},
            (1 : B) ⊗ₜ[𝒪] v' ∉
              D.line M' ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))} := by
      ext 𝔮
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, DeligneDatum.EdgeNondegAt]
      exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hc.1, hc.2, h.1, h.2⟩⟩
    rw [heq]
    exact (cov_isOpen_setOf_forall_not_mem π hB M (D.line M) _).inter
      (cov_isOpen_setOf_forall_not_mem π hB M' (D.line M') _)
  · have heq : {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} = ∅ := by
      ext 𝔮
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        DeligneDatum.EdgeNondegAt]
      exact fun h => hc ⟨h.1, h.2.1⟩
    rw [heq]
    exact isOpen_empty

end FiniteCover

namespace CerednikDrinfeld.FormalOmega

/-- If `π` is nilpotent in `B` and the residue field is finite, then after a finite Zariski cover
of `B` and a pullback along some `h ∈ GL₂(K)` on each piece, a Deligne datum lies in the edge
chart of the standard edge `g 𝒪² ⊆ 𝒪²`. -/
theorem DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤)
      (h : Fin k → Matrix.GeneralLinearGroup (Fin 2) K),
      ∀ (i : Fin k) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
        [IsLocalization.Away (f i) C],
        ∃ d' : DeligneDatum (K := K) π C,
          DeligneDatum.IsPullback (K := K) (π := π) C (h i)
            (d.map π (IsScalarTower.toAlgHom 𝒪 B C)) d' ∧
          d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
  classical
  have hloc : ∀ 𝔭 : PrimeSpectrum B, ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      (DeligneDatum.pullback π B h d).EdgeNondegAt π 𝔭.asIdeal
        (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
    intro 𝔭
    let Bp := Localization.AtPrime 𝔭.asIdeal
    have hBp : IsNilpotent (algebraMap 𝒪 Bp π) := by
      rw [IsScalarTower.algebraMap_apply 𝒪 B Bp]
      exact hB.map _
    obtain ⟨h, d', hpb, hch⟩ :=
      DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing π hπ g hg Bp hBp
        (d.map π (IsScalarTower.toAlgHom 𝒪 B Bp))
    refine ⟨h, ?_⟩
    have hd' : d' = DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B Bp)
        (DeligneDatum.pullback π B h d) := by
      rw [DeligneDatum.map_pullback]
      exact DeligneDatum.ext' (funext hpb)
    have hmax := hch (IsLocalRing.maximalIdeal Bp) inferInstance
    rw [hd'] at hmax
    have := cov_edgeNondegAt_of_map π (IsScalarTower.toAlgHom 𝒪 B Bp) _ _ _ _ hmax
    rwa [show Ideal.comap (IsScalarTower.toAlgHom 𝒪 B Bp) (IsLocalRing.maximalIdeal Bp) =
      𝔭.asIdeal from Localization.AtPrime.under_maximalIdeal (I := 𝔭.asIdeal)] at this
  choose hsel hhsel using hloc
  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun 𝔭 =>
    {𝔮 | (DeligneDatum.pullback π B (hsel 𝔭) d).EdgeNondegAt π 𝔮.asIdeal
      (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)}
  have hUopen : ∀ 𝔭, IsOpen (U 𝔭) := fun 𝔭 => cov_isOpen_setOf_edgeNondegAt π hB _ _ _
  have hUmem : ∀ 𝔭, 𝔭 ∈ U 𝔭 := fun 𝔭 => hhsel 𝔭
  have hbasic : ∀ 𝔭 : PrimeSpectrum B, ∃ f : B,
      𝔭 ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ U 𝔭 := by
    intro 𝔭
    obtain ⟨_, ⟨f, rfl⟩, hmem, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hUmem 𝔭)
        (hUopen 𝔭)
    exact ⟨f, hmem, hsub⟩
  choose fsel hfmem hfsub using hbasic
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun 𝔭 : PrimeSpectrum B => (PrimeSpectrum.basicOpen (fsel 𝔭) : Set (PrimeSpectrum B)))
    (fun 𝔭 => (PrimeSpectrum.basicOpen _).isOpen) (fun 𝔭 _ => Set.mem_iUnion.2 ⟨𝔭, hfmem 𝔭⟩)
  let k := t.card
  let e : Fin k ≃ ↥t := t.equivFin.symm
  let f : Fin k → B := fun i => fsel (e i)
  let hh : Fin k → Matrix.GeneralLinearGroup (Fin 2) K := fun i => hsel (e i)
  have hcover : ∀ 𝔮 : PrimeSpectrum B, ∃ i : Fin k,
      𝔮 ∈ (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum B)) := by
    intro 𝔮
    obtain ⟨𝔭, h𝔭⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ 𝔮))
    obtain ⟨h𝔭t, h𝔮⟩ := Set.mem_iUnion.1 h𝔭
    exact ⟨e.symm ⟨𝔭, h𝔭t⟩, by simpa [f] using h𝔮⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
    intro 𝔮 _
    obtain ⟨i, hi⟩ := hcover 𝔮
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine ⟨k, f, hspan, hh, ?_⟩
  intro i C _ _ _ _ _
  refine ⟨DeligneDatum.pullback π C (hh i) (d.map π (IsScalarTower.toAlgHom 𝒪 B C)),
    fun M => rfl, ?_⟩
  intro Q hQ
  have hfi : f i ∉ Ideal.comap (algebraMap B C) Q := by
    intro hmem
    rw [Ideal.mem_comap] at hmem
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (IsLocalization.Away.algebraMap_isUnit (f i)))
  let 𝔮 : PrimeSpectrum B := ⟨Ideal.comap (algebraMap B C) Q, Ideal.IsPrime.comap _⟩
  have h𝔮U : 𝔮 ∈ U (e i) :=
    hfsub (e i) (show 𝔮 ∈ (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum B)) from hfi)
  obtain ⟨c1, c2, c3, c4⟩ := h𝔮U
  have hmp : DeligneDatum.pullback π C (hh i) (d.map π (IsScalarTower.toAlgHom 𝒪 B C)) =
      DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B C) (DeligneDatum.pullback π B (hh i) d) := by
    rw [DeligneDatum.map_pullback]
  rw [hmp]
  refine ⟨c1, c2, fun v hv => ?_, fun v' hv' => ?_⟩
  · have := rTensor_not_mem_lineBaseChange_sup (IsScalarTower.toAlgHom 𝒪 B C) (stdFullLattice K)
      ((DeligneDatum.pullback π B (hh i) d).line (stdFullLattice K))
      ((DeligneDatum.pullback π B (hh i) d).invertible _) Q ((1 : B) ⊗ₜ[𝒪] v) (c3 v hv)
    rwa [rTensor_one_tmul] at this
  · have := rTensor_not_mem_lineBaseChange_sup (IsScalarTower.toAlgHom 𝒪 B C)
      (FullLattice.act g (stdFullLattice K))
      ((DeligneDatum.pullback π B (hh i) d).line _)
      ((DeligneDatum.pullback π B (hh i) d).invertible _) Q ((1 : B) ⊗ₜ[𝒪] v') (c4 v' hv')
    rwa [rTensor_one_tmul] at this

end CerednikDrinfeld.FormalOmega

private theorem pb_comap_sup_smul_top {B : Type} [CommRing B] {V W : Type} [AddCommGroup V]
    [AddCommGroup W] [Module B V] [Module B W]
    (Φ : V ≃ₗ[B] W) (S : Submodule B W) (𝔭 : Ideal B) :
    (S ⊔ 𝔭 • ⊤).comap Φ.toLinearMap = S.comap Φ.toLinearMap ⊔ 𝔭 • ⊤ := by
  rw [Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup,
    Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

private theorem pb_edgeNondegAt_act_of_isPullback
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {π : 𝒪} (h : Matrix.GeneralLinearGroup (Fin 2) K) {d d' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h d d')
    {M' M : FullLattice 𝒪 K} (𝔭 : Ideal B) (hd' : d'.EdgeNondegAt π 𝔭 M' M) :
    d.EdgeNondegAt π 𝔭 (FullLattice.act h M') (FullLattice.act h M) := by
  obtain ⟨hle, hπ, h1, h2⟩ := hd'
  refine ⟨latticeMap_mono h hle, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    rw [← hwv, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
  · intro v hv hmem
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    have hw' : (w : Fin 2 → K) ∉ M'.1 := by
      intro hw'
      apply hv
      rw [← hwv]
      exact mulVec_mem_latticeMap hw'
    apply h1 ⟨w, hw⟩ hw'
    rw [hd M, ← pb_comap_sup_smul_top, Submodule.mem_comap]
    have key : (actBaseChange B h M).toLinearMap ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥M.1)) =
        (1 : B) ⊗ₜ[𝒪] v := by
      change (1 : B) ⊗ₜ[𝒪] latticeMapEquiv h M.1 ⟨w, hw⟩ = (1 : B) ⊗ₜ[𝒪] v
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply]
      exact hwv
    rw [key]
    exact hmem
  · intro v' hv' hmem
    obtain ⟨w', hw', hwv'⟩ := mem_latticeMap.mp v'.2
    have hnd : ¬ ∃ u : ↥M.1, ((⟨w', hw'⟩ : ↥M'.1) : Fin 2 → K) =
        algebraMap 𝒪 K π • (u : Fin 2 → K) := by
      rintro ⟨u, hu⟩
      apply hv'
      refine ⟨⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ (u : Fin 2 → K), mulVec_mem_latticeMap u.2⟩, ?_⟩
      change (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (u : Fin 2 → K))
      rw [← Matrix.mulVec_smul, ← hwv']
      exact congrArg _ hu
    apply h2 ⟨w', hw'⟩ hnd
    rw [hd M', ← pb_comap_sup_smul_top, Submodule.mem_comap]
    have key : (actBaseChange B h M').toLinearMap ((1 : B) ⊗ₜ[𝒪] (⟨w', hw'⟩ : ↥M'.1)) =
        (1 : B) ⊗ₜ[𝒪] v' := by
      change (1 : B) ⊗ₜ[𝒪] latticeMapEquiv h M'.1 ⟨w', hw'⟩ = (1 : B) ⊗ₜ[𝒪] v'
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply]
      exact hwv'
    rw [key]
    exact hmem

/-- If `d'` is the pullback of `d` along `h` and `d'` is in the edge chart of `M' ⊆ M`, then `d`
is in the edge chart of `h M' ⊆ h M`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_of_isPullback
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) {d d' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h d d')
    {M' M : FullLattice 𝒪 K} (hd' : d'.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act h M') (FullLattice.act h M) :=
  fun 𝔭 h𝔭 => pb_edgeNondegAt_act_of_isPullback h hd 𝔭 (hd' 𝔭 h𝔭)

private theorem map_sup_smul_top' {B : Type} [CommRing B] {V W : Type} [AddCommGroup V]
    [AddCommGroup W] [Module B V] [Module B W]
    (Φ : V ≃ₗ[B] W) (S : Submodule B V) (𝔭 : Ideal B) :
    (S ⊔ 𝔭 • ⊤).map Φ.toLinearMap = S.map Φ.toLinearMap ⊔ 𝔭 • ⊤ := by
  rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

private theorem swap_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {π : 𝒪} (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (𝔭 : Ideal B)
    (hd : d.EdgeNondegAt π 𝔭 M' M) :
    d.EdgeNondegAt π 𝔭 (FullLattice.act (scalarGL c) M) M' := by
  obtain ⟨hle, hπ, h1, h2⟩ := hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
    rw [← hwv, hc]
    exact hπ ⟨w, hw⟩
  · intro v
    exact mem_latticeMap_scalarGL.mpr ⟨v, hle v.2, by rw [hc]⟩
  · intro v hv
    apply h2 v
    rintro ⟨w, hw⟩
    apply hv
    exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, by rw [hc]; exact hw.symm⟩
  · intro v' hv' hmem
    obtain ⟨u, hu, huv⟩ := mem_latticeMap_scalarGL.mp v'.2
    have hu' : (u : Fin 2 → K) ∉ M'.1 := by
      intro h
      exact hv' ⟨⟨u, h⟩, by rw [← huv, hc]⟩
    apply h1 ⟨u, hu⟩ hu'
    rw [d.homothety c M, ← map_sup_smul_top'] at hmem
    have key : actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] (⟨u, hu⟩ : ↥M.1)) =
        (1 : B) ⊗ₜ[𝒪] v' := by
      change (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 ⟨u, hu⟩ = (1 : B) ⊗ₜ[𝒪] v'
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
      exact huv
    rw [← key, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at hmem
    exact hmem

/-- The edge chart of `M' ⊆ M` equals the edge chart of the swapped edge `π M ⊆ M'`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M) M' :=
  fun 𝔭 h𝔭 => swap_edgeNondegAt c hc 𝔭 (hd 𝔭 h𝔭)

/-- By the homothety axiom, a Deligne datum is its own pullback along a scalar matrix. -/
private theorem isPullback_scalarGL_self
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (c : Kˣ) :
    DeligneDatum.IsPullback (K := K) (π := π) B (scalarGL c) d d := by
  intro M
  rw [d.homothety c M,
    Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL c) M).injective]

private theorem act_scalarGL_inv_act
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (c : Kˣ)
    (M : FullLattice 𝒪 K) :
    FullLattice.act (scalarGL c⁻¹) (FullLattice.act (scalarGL c) M) = M := by
  apply Subtype.ext
  change latticeMap (scalarGL c⁻¹) (latticeMap (scalarGL c) M.1) = M.1
  rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]

/-- The edge chart is invariant under scaling both lattices of the edge by `c ∈ Kˣ`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B]
    [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (c : Kˣ) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M') (FullLattice.act (scalarGL c) M) ↔
      d.InEdgeChart π M' M := by
  refine ⟨fun h => ?_, fun h =>
    DeligneDatum.inEdgeChart_act_of_isPullback (scalarGL c) (isPullback_scalarGL_self d c) h⟩
  have := DeligneDatum.inEdgeChart_act_of_isPullback (scalarGL c⁻¹)
    (isPullback_scalarGL_self d c⁻¹) h
  rwa [act_scalarGL_inv_act, act_scalarGL_inv_act] at this

section DetIndex

private theorem nil_exists_unit_mul_zpow_of_ne_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : 𝒪ˣ), x = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
  refine ⟨(i : ℤ) - j, ua⁻¹ * ub, ?_⟩
  have ha : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K (ua⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hua, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hb' : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hub, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hubK : algebraMap 𝒪 K (ub : 𝒪ˣ) ≠ 0 := by
    intro h
    apply ub.ne_zero
    exact IsFractionRing.injective 𝒪 K (by rw [h, map_zero])
  have hBi : algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) = (algebraMap 𝒪 K (ub : 𝒪ˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', hBi, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
  field_simp

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

/-- The diagonal matrix `diag(a, 1)`. -/
private def nilDiagFst (a : Kˣ) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![(a : K), 1], Matrix.diagonal ![((a⁻¹ : Kˣ) : K), 1], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

private theorem nilDiagFst_coe (a : Kˣ) :
    ((nilDiagFst a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(a : K), 1] :=
  rfl

private theorem nilDiagFst_mulVec (a : Kˣ) (v : Fin 2 → K) :
    ((nilDiagFst a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![(a : K) * v 0, v 1] := by
  rw [nilDiagFst_coe]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

private theorem nil_latticeMap_diagFst_le [IsFractionRing 𝒪 K] {π : 𝒪} (c : Kˣ)
    (hc : (c : K) = algebraMap 𝒪 K π) :
    latticeMap (nilDiagFst c) (stdLattice 𝒪 K) ≤ stdLattice 𝒪 K := by
  apply latticeMap_le_stdLattice_of_isInteger
  intro i j
  rw [nilDiagFst_coe]
  fin_cases i <;> fin_cases j
  · exact ⟨π, by simp [hc]⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private theorem nil_smul_mem_latticeMap_diagFst {π : 𝒪} (c : Kˣ)
    (hc : (c : K) = algebraMap 𝒪 K π) {v : Fin 2 → K} (hv : v ∈ stdLattice 𝒪 K) :
    algebraMap 𝒪 K π • v ∈ latticeMap (nilDiagFst c) (stdLattice 𝒪 K) := by
  refine mem_latticeMap.mpr ⟨![v 0, algebraMap 𝒪 K π * v 1], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hv 0
    · obtain ⟨r, hr⟩ := hv 1
      exact ⟨π * r, by simp [← hr]⟩
  · rw [nilDiagFst_mulVec, hc]
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

private theorem nil_smul_mem_latticeMap_of_forall {π : 𝒪} (l : GL (Fin 2) K)
    {S L : Submodule 𝒪 (Fin 2 → K)}
    (h : ∀ v ∈ L, algebraMap 𝒪 K π • v ∈ S) {v : Fin 2 → K} (hv : v ∈ latticeMap l L) :
    algebraMap 𝒪 K π • v ∈ latticeMap l S := by
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  rw [← Matrix.mulVec_smul]
  exact mulVec_mem_latticeMap (h w hw)

omit [Field K] in
private theorem nil_val_det_scalarGL {K : Type} [Field K] (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL a) : Kˣ) : K) = (a : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

private theorem nil_val_det_diagFst (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (nilDiagFst a) : Kˣ) : K) = (a : K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, nilDiagFst_coe, Matrix.det_diagonal]
  simp

variable [IsFractionRing 𝒪 K] {π : 𝒪}
variable {C : Type} [CommRing C] [Algebra 𝒪 C]

private theorem nil_rescale (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    (e : DeligneDatum (K := K) π C)
    (s : GL (Fin 2) K) (S L : FullLattice 𝒪 K) (hS : S.1 = latticeMap s (stdLattice 𝒪 K))
    (hSL : S.1 ≤ L.1) (hπL : ∀ v ∈ L.1, algebraMap 𝒪 K π • v ∈ S.1) (hch : e.InEdgeChart π S L)
    (m : ℤ) (u : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det s : Kˣ) : K) =
      algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ (2 * m)) :
    ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧
      HasDetIndex π M'.1 0 ∧ e.InEdgeChart π M' M := by
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  refine ⟨FullLattice.act (scalarGL (c ^ (-m))) S, FullLattice.act (scalarGL (c ^ (-m))) L,
    latticeMap_mono _ hSL, ?_, ?_,
    (DeligneDatum.inEdgeChart_act_scalarGL_iff e S L (c ^ (-m))).mpr hch⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [smul_comm]
    exact mem_latticeMap_scalarGL.mpr ⟨_, hπL w hw, rfl⟩
  · refine ⟨scalarGL (c ^ (-m)) * s, ?_, u, ?_⟩
    · change latticeMap (scalarGL (c ^ (-m)) * s) (stdLattice 𝒪 K) =
        latticeMap (scalarGL (c ^ (-m))) S.1
      rw [latticeMap_mul, hS]
    · rw [map_mul, Units.val_mul, nil_val_det_scalarGL, hdet, Units.val_zpow_eq_zpow_val, hc,
        zpow_zero, mul_one]
      have h1 : (algebraMap 𝒪 K π ^ (-m)) ^ 2 * algebraMap 𝒪 K π ^ (2 * m) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπK,
          show -m * ((2 : ℕ) : ℤ) + 2 * m = 0 by push_cast; ring, zpow_zero]
      calc (algebraMap 𝒪 K π ^ (-m)) ^ 2 * (algebraMap 𝒪 K ↑u * algebraMap 𝒪 K π ^ (2 * m))
          = algebraMap 𝒪 K ↑u * ((algebraMap 𝒪 K π ^ (-m)) ^ 2 * algebraMap 𝒪 K π ^ (2 * m)) := by
            ring
        _ = algebraMap 𝒪 K ↑u := by rw [h1, mul_one]

private theorem nil_orient (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    (e : DeligneDatum (K := K) π C) (l : GL (Fin 2) K) (n : ℤ) (u : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det l : Kˣ) : K) =
      algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n)
    (hch : e.InEdgeChart π (FullLattice.act l (FullLattice.act (nilDiagFst c) (stdFullLattice K)))
      (FullLattice.act l (stdFullLattice K))) :
    ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧
      HasDetIndex π M'.1 0 ∧ e.InEdgeChart π M' M := by
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  set S : FullLattice 𝒪 K :=
    FullLattice.act l (FullLattice.act (nilDiagFst c) (stdFullLattice K)) with hSdef
  set L : FullLattice 𝒪 K := FullLattice.act l (stdFullLattice K) with hLdef
  have hS : S.1 = latticeMap (l * nilDiagFst c) (stdLattice 𝒪 K) := by
    rw [hSdef, latticeMap_mul]
    rfl
  have hL : L.1 = latticeMap l (stdLattice 𝒪 K) := by
    rw [hLdef]
    rfl
  have hSL : S.1 ≤ L.1 := by
    rw [hSdef, hLdef]
    exact latticeMap_mono l (nil_latticeMap_diagFst_le c hc)
  have hπL : ∀ v ∈ L.1, algebraMap 𝒪 K π • v ∈ S.1 := by
    rw [hSdef, hLdef]
    intro v hv
    exact nil_smul_mem_latticeMap_of_forall l
      (fun w hw => nil_smul_mem_latticeMap_diagFst c hc hw) hv
  rcases Int.even_or_odd' n with ⟨m, hm | hm⟩
  · have hch' := DeligneDatum.inEdgeChart_swap c hc hch
    refine nil_rescale hπ c hc e (scalarGL c * l) (FullLattice.act (scalarGL c) L) S ?_ ?_ ?_
      hch' (m + 1) u ?_
    · change latticeMap (scalarGL c) L.1 = _
      rw [hL, latticeMap_mul]
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
      rw [hc]
      exact hπL w hw
    · intro v hv
      rw [← hc]
      exact mem_latticeMap_scalarGL.mpr ⟨v, hSL hv, rfl⟩
    · rw [map_mul, Units.val_mul, nil_val_det_scalarGL, hdet, hc, hm]
      rw [← zpow_natCast, mul_left_comm, ← zpow_add₀ hπK]
      congr 2
      push_cast
      ring
  · refine nil_rescale hπ c hc e (l * nilDiagFst c) S L hS hSL hπL hch (m + 1) u ?_
    rw [map_mul, Units.val_mul, nil_val_det_diagFst, hdet, hc, hm, mul_assoc,
      ← zpow_add_one₀ hπK]
    congr 2
    ring

end DetIndex

namespace CerednikDrinfeld.FormalOmega

/-- If `π` is nilpotent in `B` and the residue field is finite, then on a finite Zariski cover of
`B` a Deligne datum lies in the edge chart of some edge `π M ⊆ M' ⊆ M` with `M'` of determinant
index `0`. -/
theorem DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (M' M : Fin k → FullLattice 𝒪 K),
      ∀ i : Fin k, (M' i).1 ≤ (M i).1 ∧ (∀ v ∈ (M i).1, algebraMap 𝒪 K π • v ∈ (M' i).1) ∧
        HasDetIndex π (M' i).1 0 ∧
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π
          (M' i) (M i) := by
  classical
  have hc : ((unitOfNeZero (K := K) hπ.ne_zero : Kˣ) : K) = algebraMap 𝒪 K π :=
    unitOfNeZero_coe hπ.ne_zero
  have hg : ((nilDiagFst (unitOfNeZero (K := K) hπ.ne_zero) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1] := by
    rw [nilDiagFst_coe, hc]
  obtain ⟨k, f, hf, h, H⟩ :=
    DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite π hπ
      (nilDiagFst (unitOfNeZero (K := K) hπ.ne_zero)) hg B hB d
  have key : ∀ i : Fin k, ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧
      (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧ HasDetIndex π M'.1 0 ∧
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π M' M := by
    intro i
    obtain ⟨d', hpb, hch⟩ := H i (Localization.Away (f i))
    obtain ⟨n, u, hdet⟩ := nil_exists_unit_mul_zpow_of_ne_zero hπ
      (Units.ne_zero (Matrix.GeneralLinearGroup.det (h i)))
    exact nil_orient hπ _ hc _ (h i) n u hdet
      (DeligneDatum.inEdgeChart_act_of_isPullback (h i) hpb hch)
  exact ⟨k, f, hf, fun i => (key i).choose, fun i => (key i).choose_spec.choose,
    fun i => (key i).choose_spec.choose_spec⟩

end CerednikDrinfeld.FormalOmega

private theorem vh_vertexNondegAt_of_act
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (π : 𝒪) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ) (M : FullLattice 𝒪 K)
    (H : d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) M)) : d.VertexNondegAt π 𝔭 M := by
  intro v hv hmem
  have hcv : (c : K) • (v : Fin 2 → K) ∈ (FullLattice.act (scalarGL c) M).1 :=
    mem_latticeMap_scalarGL.mpr ⟨v, v.2, rfl⟩
  apply H ⟨(c : K) • (v : Fin 2 → K), hcv⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨w, hw, hww'⟩ := mem_latticeMap_scalarGL.mp w'.2
    apply hv
    refine ⟨⟨w, hw⟩, ?_⟩
    have h1 : (c : K) • (v : Fin 2 → K) = (c : K) • (algebraMap 𝒪 K π • w) := by
      rw [smul_comm, hww']
      exact hw'
    exact smul_right_injective _ c.ne_zero h1
  · rw [d.homothety c M, ← map_sup_smul_top']
    have key : actBaseChange B (scalarGL c) M ((1 : B) ⊗ₜ[𝒪] v) =
        (1 : B) ⊗ₜ[𝒪] (⟨(c : K) • (v : Fin 2 → K), hcv⟩ :
          ↥(FullLattice.act (scalarGL c) M).1) := by
      change (1 : B) ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) M.1 v = _
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
    rw [← key]
    exact Submodule.mem_map_of_mem hmem

/-- Vertex nondegeneracy is invariant under scaling the lattice by `c ∈ Kˣ`. -/
theorem CerednikDrinfeld.FormalOmega.DeligneDatum.vertexNondegAt_act_scalarGL_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ)
    (M : FullLattice 𝒪 K) :
    d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) M) ↔ d.VertexNondegAt π 𝔭 M := by
  refine ⟨vh_vertexNondegAt_of_act π d 𝔭 c M, fun h => ?_⟩
  have := vh_vertexNondegAt_of_act π d 𝔭 c⁻¹ (FullLattice.act (scalarGL c) M)
  rw [act_scalarGL_inv_act] at this
  exact this h

end
