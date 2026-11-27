/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.HeegnerIdeal
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The Heegner isogeny is cyclic of degree `N`

For an imaginary quadratic field `K` with a complex embedding `σ : K →+* ℂ`, the image `σ(I)` of a
nonzero fractional ideal `I` of `𝓞 K` is a lattice in `ℂ`
(`NumberField.FractionalIdeal.isZLattice_complexLattice`). For a nonzero ideal `𝒩` of `𝓞 K` with
`𝓞 K ⧸ 𝒩` cyclic of order `N`, the map `ℂ / σ(𝓞 K) → ℂ / σ(𝒩⁻¹)` induced by the identity is
surjective with kernel `σ(𝒩⁻¹) / σ(𝓞 K) ≃ 𝓞 K ⧸ 𝒩`, cyclic of order `N`
(`NumberField.FractionalIdeal.heegner_isogeny_isAddCyclic_ker`). These are the complex tori whose
pair defines the Heegner point `x₁` on `X₀(N)` (Gross, *Kolyvagin's work on modular elliptic
curves*, 1991, §1, p. 235; Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific
elliptic curves of analytic rank zero and one*, 2011, §4, p. 335).

## Proof

`K` has exactly one infinite place, so every complex embedding gives the same absolute value, and
`NumberField.Embeddings.finite_of_norm_le` shows that `σ(I)` meets each ball in finitely many
points. Since `σ` is not real, `σ(𝓞 K)` contains a non-real number, so `σ(I)` spans `ℂ` over `ℝ`.
The kernel of `ℂ / σ(𝓞 K) → ℂ / σ(𝒩⁻¹)` is `σ(𝒩⁻¹) / σ(𝓞 K)`, which `σ` identifies with
`𝒩⁻¹ / 𝓞 K ≃ 𝓞 K ⧸ 𝒩` (`FractionalIdeal.invQuotientEquiv`).
-/

@[expose] public section

open NumberField nonZeroDivisors

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- For submodules `p ≤ q` of `M`, the kernel of the map `M ⧸ p → M ⧸ q` induced by the identity is
isomorphic to `q ⧸ p`. -/
noncomputable def kerMapQIdEquiv {p q : Submodule R M} (h : p ≤ q) :
    (LinearMap.ker (p.mapQ q LinearMap.id h)) ≃ₗ[R] (q ⧸ p.comap q.subtype) :=
  let f : q →ₗ[R] M ⧸ p := p.mkQ ∘ₗ q.subtype
  have hker : LinearMap.ker f = p.comap q.subtype := by
    rw [LinearMap.ker_comp, ker_mkQ]
  have hrange : LinearMap.range f = LinearMap.ker (p.mapQ q LinearMap.id h) := by
    rw [LinearMap.range_comp, range_subtype, ker_mapQ, comap_id]
  (LinearEquiv.ofEq _ _ hrange.symm).trans
    ((f.quotKerEquivRange.symm).trans (quotEquivOfEq _ _ hker))

end Submodule

namespace NumberField.FractionalIdeal

variable {K : Type*} [Field K] [NumberField K]

/-- The image `σ(I) ⊆ ℂ` of a fractional ideal `I` of `𝓞 K`, as a `ℤ`-submodule of `ℂ`. -/
noncomputable def complexLattice (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule ℤ ℂ :=
  ((I : Submodule (𝓞 K) K).restrictScalars ℤ).map σ.toAddMonoidHom.toIntLinearMap

/-- In a totally complex field of degree `2`, all complex embeddings induce the same norm. -/
theorem norm_embedding_eq [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (σ φ : K →+* ℂ) (x : K) : ‖φ x‖ = ‖σ x‖ := by
  have h₁ := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h₂ := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, hK] at h₁
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K] at h₂
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  rw [← InfinitePlace.apply, ← InfinitePlace.apply, Subsingleton.elim (InfinitePlace.mk φ)]

/-- The image of a fractional ideal of an imaginary quadratic field under a complex embedding is
discrete in `ℂ`. -/
theorem discreteTopology_complexLattice [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) : DiscreteTopology (complexLattice σ I) := by
  obtain ⟨a, ha, hI⟩ := I.isFractional
  set c : ℂ := σ (algebraMap (𝓞 K) K a)
  have hc : c ≠ 0 := by
    simpa [c] using nonZeroDivisors.ne_zero ha
  set F := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ ‖c‖}
  have hF : F.Finite := Embeddings.finite_of_norm_le K ℂ ‖c‖
  set T : Set ℂ := (fun x ↦ σ x / c) '' F
  have hT : T.Finite := hF.image _
  have hsub : ∀ z ∈ complexLattice σ I, ‖z‖ ≤ 1 → z ∈ T := by
    rintro z ⟨b, hb, rfl⟩ hz
    obtain ⟨y, hy⟩ := hI b hb
    refine ⟨algebraMap (𝓞 K) K a * b, ⟨?_, fun φ ↦ ?_⟩, ?_⟩
    · rw [← Algebra.smul_def, ← hy]
      exact RingOfIntegers.isIntegral_coe y
    · rw [norm_embedding_eq hK σ φ, map_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hz
    · simp [c, hc]
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨Metric.ball 0 1 ∩ (T \ {0})ᶜ,
    Metric.isOpen_ball.inter (hT.sdiff.isClosed.isOpen_compl), ?_⟩
  ext ⟨z, hz⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not,
    Submodule.mk_eq_zero]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact h₂ (hsub z hz h₁.le)
  · rintro rfl
    simp

/-- The image of a nonzero fractional ideal of a totally complex field under a complex embedding
spans `ℂ` over `ℝ`. -/
theorem span_complexLattice [IsTotallyComplex K] (σ : K →+* ℂ) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) : Submodule.span ℝ (complexLattice σ I : Set ℂ) = ⊤ := by
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra! h
    exact hI (FractionalIdeal.ext fun x ↦ ⟨fun hx ↦ by simp [h x hx], fun hx ↦ by
      rw [FractionalIdeal.mem_zero_iff] at hx
      exact hx ▸ (I : Submodule (𝓞 K) K).zero_mem⟩)
  have hnr : ¬ ComplexEmbedding.IsReal σ :=
    InfinitePlace.isComplex_mk_iff.mp ((isTotallyComplex_iff K).mp ‹_› _)
  obtain ⟨k, hk⟩ : ∃ k : K, (σ k).im ≠ 0 := by
    by_contra! h
    exact hnr (RingHom.ext fun k ↦ Complex.conj_eq_iff_im.mpr (h k))
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) k
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 K, (σ (algebraMap _ K y)).im ≠ 0 := by
    by_contra! h
    apply hk
    rw [map_div₀, Complex.div_im, h p, h q]
    simp
  set W := Submodule.span ℝ (complexLattice σ I : Set ℂ)
  have mem : ∀ z : 𝓞 K, σ x * σ (algebraMap _ K z) ∈ W := fun z ↦
    Submodule.subset_span ⟨algebraMap _ K z * x, (I : Submodule (𝓞 K) K).smul_mem z hxI,
      by simp [mul_comm]⟩
  have h₁ : σ x ∈ W := by simpa using mem 1
  have h₂ := mem y
  set c := σ x
  set w := σ (algebraMap _ K y)
  have hc : c ≠ 0 := (map_ne_zero σ).mpr hx0
  rw [Submodule.eq_top_iff']
  intro v
  set u := v / c
  have hu : u = ((u.re - u.im / w.im * w.re : ℝ) : ℂ) + ((u.im / w.im : ℝ) : ℂ) * w := by
    apply Complex.ext <;> simp; field_simp
  have hv : v = (u.re - u.im / w.im * w.re) • c + (u.im / w.im) • (c * w) := by
    rw [Complex.real_smul, Complex.real_smul]
    calc v = c * u := (mul_div_cancel₀ v hc).symm
      _ = c * (((u.re - u.im / w.im * w.re : ℝ) : ℂ) + ((u.im / w.im : ℝ) : ℂ) * w) :=
        congrArg (c * ·) hu
      _ = _ := by ring
  rw [hv]
  exact W.add_mem (W.smul_mem _ h₁) (W.smul_mem _ h₂)

/-- The image of a nonzero fractional ideal of an imaginary quadratic field under a complex
embedding is a `ℤ`-lattice in `ℂ`. -/
theorem isZLattice_complexLattice [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∃ _ : DiscreteTopology (complexLattice σ I), IsZLattice ℝ (complexLattice σ I) := by
  have := discreteTopology_complexLattice hK σ I
  exact ⟨this, ⟨span_complexLattice σ hI⟩⟩

omit [NumberField K] in
/-- A complex number lies in `σ(I)` if and only if it is `σ x` for some `x ∈ I`. -/
theorem mem_complexLattice {σ : K →+* ℂ} {I : FractionalIdeal (𝓞 K)⁰ K} {z : ℂ} :
    z ∈ complexLattice σ I ↔ ∃ x ∈ I, σ x = z := by
  simp [complexLattice]

omit [NumberField K] in
/-- `I ↦ σ(I)` is monotone. -/
theorem complexLattice_mono (σ : K →+* ℂ) {I J : FractionalIdeal (𝓞 K)⁰ K} (h : I ≤ J) :
    complexLattice σ I ≤ complexLattice σ J :=
  Submodule.map_mono (by simpa using h)

/-- The embedding `σ` as an additive isomorphism from a fractional ideal `I` onto `σ(I)`. -/
noncomputable def complexLatticeEquiv (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (I : Submodule (𝓞 K) K) ≃ₗ[ℤ] complexLattice σ I :=
  let f : (I : Submodule (𝓞 K) K) →+ complexLattice σ I :=
    { toFun := fun x => ⟨σ (x : K), mem_complexLattice.mpr ⟨x, x.2, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ (x : K) (y : K)) }
  LinearEquiv.ofBijective f.toIntLinearMap
    ⟨fun x y hxy => Subtype.ext (σ.injective (congrArg Subtype.val hxy)), fun ⟨z, hz⟩ => by
      obtain ⟨x, hx, rfl⟩ := mem_complexLattice.mp hz
      exact ⟨⟨x, hx⟩, rfl⟩⟩

/-- For fractional ideals `J ≤ I`, the embedding `σ` identifies `I / J` with `σ(I) / σ(J)`. -/
noncomputable def quotientEquivComplexLatticeQuotient (σ : K →+* ℂ)
    (I J : FractionalIdeal (𝓞 K)⁰ K) :
    ((I : Submodule (𝓞 K) K) ⧸ (J : Submodule (𝓞 K) K).comap (I : Submodule (𝓞 K) K).subtype)
      ≃ₗ[ℤ]
      (complexLattice σ I ⧸ (complexLattice σ J).comap (complexLattice σ I).subtype) :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ _).symm.trans
    (Submodule.Quotient.equiv _ _ (complexLatticeEquiv σ I) (by
      ext ⟨z, hz⟩
      obtain ⟨x, hx, rfl⟩ := mem_complexLattice.mp hz
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact mem_complexLattice.mpr ⟨y, hy, congrArg Subtype.val hyx⟩
      · intro h
        obtain ⟨w, hw, hwx⟩ := mem_complexLattice.mp h
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        change x ∈ (J : Submodule (𝓞 K) K)
        rwa [← σ.injective hwx]))

/-- **The Heegner isogeny is cyclic of degree `N`.** Let `K ⊂ ℂ` be an imaginary quadratic field,
embedded by `σ : K →+* ℂ`, with ring of integers `𝓞 K`, and let `𝒩` be a nonzero ideal of `𝓞 K`
such that `𝓞 K ⧸ 𝒩` is cyclic of order `N`. Let `𝒩⁻¹ = {x ∈ K : x 𝒩 ⊆ 𝓞 K}` (Mathlib's inverse
of fractional ideals, `FractionalIdeal.mem_inv_iff`). Then `σ(𝓞 K)` and `σ(𝒩⁻¹)` are lattices in
`ℂ` (discrete `ℤ`-submodules spanning `ℂ` over `ℝ`) with `σ(𝓞 K) ⊆ σ(𝒩⁻¹)`, the quotient
`σ(𝒩⁻¹) / σ(𝓞 K)` is cyclic of order `N`, and the map `ℂ / σ(𝓞 K) → ℂ / σ(𝒩⁻¹)` induced by the
identity of `ℂ` is surjective with kernel `σ(𝒩⁻¹) / σ(𝓞 K)`, cyclic of order `N`.

Here `𝓞 K` is the unit fractional ideal `1`, and an isogeny of complex tori is expressed by the
surjective group homomorphism of the quotients with finite kernel; the complex structure of the
tori is not stated.

Sources: R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic
curves of analytic rank zero and one*, LMS J. Comput. Math. 14 (2011), 327–350, §4, p. 335
("Since $\mathcal{O}_K \subset \mathcal{N}^{-1}$, we have a cyclic $N$-isogeny
$\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$ of elliptic curves with CM by
$\mathcal{O}_K$"); B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and
arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
235–256, §1, p. 235 (the complex tori $\mathbb{C}/\mathcal{O}$ and $\mathbb{C}/\mathcal{N}^{-1}$
"define elliptic curves related by a cyclic $N$-isogeny"). -/
theorem heegner_isogeny_isAddCyclic_ker [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) {𝒩 : Ideal (𝓞 K)} (h𝒩 : 𝒩 ≠ ⊥) {N : ℕ} (hcyc : IsAddCyclic (𝓞 K ⧸ 𝒩))
    (hcard : Nat.card (𝓞 K ⧸ 𝒩) = N) :
    (∃ _ : DiscreteTopology (complexLattice σ 1), IsZLattice ℝ (complexLattice σ 1)) ∧
    (∃ _ : DiscreteTopology (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
      IsZLattice ℝ (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) ∧
    ∃ h : complexLattice σ 1 ≤ complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      IsAddCyclic (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ⧸ (complexLattice σ 1).comap
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹).subtype) ∧
      Nat.card (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ⧸ (complexLattice σ 1).comap
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹).subtype) = N ∧
      Function.Surjective ((complexLattice σ 1).mapQ
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) LinearMap.id h) ∧
      IsAddCyclic (LinearMap.ker ((complexLattice σ 1).mapQ
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) LinearMap.id h)) ∧
      Nat.card (LinearMap.ker ((complexLattice σ 1).mapQ
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) LinearMap.id h)) = N := by
  have h𝒩0 : (𝒩 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_eq_zero.not.mpr h𝒩
  have hle := complexLattice_mono σ (FractionalIdeal.one_le_inv_coeIdeal (L := K) h𝒩)
  -- `σ(𝒩⁻¹) / σ(𝓞 K) ≃ 𝒩⁻¹ / 𝓞 K ≃ 𝓞 K ⧸ 𝒩`
  let e := ((quotientEquivComplexLatticeQuotient σ _ 1).symm.toAddEquiv).trans
    (FractionalIdeal.invQuotientEquiv (L := K) 𝒩 h𝒩).toAddEquiv
  let e' := ((Submodule.kerMapQIdEquiv hle).toAddEquiv).trans e
  refine ⟨isZLattice_complexLattice hK σ one_ne_zero,
    isZLattice_complexLattice hK σ (inv_ne_zero h𝒩0), hle,
    isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hcard, fun z => ?_,
    isAddCyclic_of_surjective e'.symm.toAddMonoidHom e'.symm.surjective,
    (Nat.card_congr e'.toEquiv).trans hcard⟩
  induction z using Submodule.Quotient.induction_on with
  | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩

end NumberField.FractionalIdeal

end
