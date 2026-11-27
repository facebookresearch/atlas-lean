/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CohCarrier_HeckeData.lean`,
`Definitions/Def_IharaLemma_IdempotentSplitting.lean`,
`Theorems/Thm_CohCarrier_HeckeData_finite_ML_and_free_ML.lean`
and
`P2M/Sol/S_CohCarrier_HeckeData_finite_ML_and_free_ML.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.LocalRing.FiniteAlgebraDecomposition

/-!
# Localized Hecke modules over complete local rings

Let `𝒪` be a complete Noetherian local ring and `V` a finite `𝒪`-module with a
family of pairwise commuting endomorphisms, each with a prescribed eigenvalue in
a field `k` (`HeckeData`). The eigenvalue character of the free commutative
`𝒪`-algebra on these operators has a prime kernel `HeckeData.mTheta`, and
`HeckeData.ML` is `V` localized there. When `mTheta` is maximal, for instance
when `algebraMap 𝒪 k` is surjective, `ML` is finite over `𝒪`, and free over `𝒪`
when `V` is.

The image of the free algebra in `Module.End 𝒪 V` is a finite `𝒪`-algebra. A
complete local ring is henselian, so a finite algebra over it is a finite product
of local rings: its maximal ideals are separated by complete orthogonal
idempotents (`IdempotentSplitting`). The localization of `V` at a maximal ideal
is then the corner `e • V` of the matching idempotent `e`, a direct summand of
`V`.

## Main declarations

* `HeckeData`, `HeckeData.mTheta`, `HeckeData.ML`: the data, the eigenvalue
  ideal and the localized module.
* `nonempty_idempotentSplitting_of_finite`: a finite algebra over a complete
  Noetherian local ring has an idempotent splitting.
* `HeckeData.finite_and_free_localizedModule_of_isMaximal`: `ML` is finite, and
  free when `V` is, whenever `mTheta` is maximal.
* `HeckeData.finite_and_free_localizedModule`: the case where `algebraMap 𝒪 k`
  is surjective.

## References

* [Stacks, Lemma 10.153.9](https://stacks.math.columbia.edu/tag/04GM): a
  complete local ring is henselian.
* [Stacks, Lemma 10.153.3 (10)](https://stacks.math.columbia.edu/tag/04GG): a
  finite algebra over a henselian local ring is a finite product of local rings.
-/

@[expose] public section

universe u v w

/-- **Hecke data.** Hecke data on an `𝒪`-module `V` is a family of pairwise
commuting endomorphisms indexed by `Gen`, together with a prescribed eigenvalue
in the field `k` for each generator. Only an `𝒪`-algebra structure on `k` is
assumed, so `k` need not be a residue field of `𝒪`. -/
structure HeckeData (𝒪 : Type u) [CommRing 𝒪] (V : Type v) [AddCommGroup V]
    [Module 𝒪 V] (k : Type w) [Field k] [Algebra 𝒪 k] where
  /-- The index type of the Hecke operators. -/
  Gen : Type
  /-- The Hecke operator attached to each generator. -/
  op : Gen → Module.End 𝒪 V
  /-- The operators pairwise commute. -/
  comm : ∀ g h : Gen, op g * op h = op h * op g
  /-- The prescribed eigenvalue of each generator. -/
  θbar : Gen → k

namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

/-- **Free algebra on the Hecke generators.** The free commutative `𝒪`-algebra
on the generators of `D`. -/
noncomputable abbrev FreeAlg : Type u := MvPolynomial D.Gen 𝒪

/-- **Eigenvalue character.** The `𝒪`-algebra map `FreeAlg →ₐ[𝒪] k` sending
each generator to its prescribed eigenvalue. -/
noncomputable def thetaTilde : D.FreeAlg →ₐ[𝒪] k := MvPolynomial.aeval D.θbar

/-- **Eigenvalue ideal.** The kernel of the eigenvalue character, a prime ideal
of `FreeAlg`. It is maximal when `thetaTilde` is surjective, for instance when
`algebraMap 𝒪 k` is, but not in general. -/
noncomputable def mTheta : Ideal D.FreeAlg := RingHom.ker D.thetaTilde.toRingHom

instance mTheta_isPrime : D.mTheta.IsPrime := RingHom.ker_isPrime _

/-- **Hecke subalgebra.** The subalgebra of `Module.End 𝒪 V` generated by the
Hecke operators. -/
noncomputable def opSubalgebra : Subalgebra 𝒪 (Module.End 𝒪 V) :=
  Algebra.adjoin 𝒪 (Set.range D.op)

theorem op_comm_of_mem : ∀ a ∈ Set.range D.op, ∀ b ∈ Set.range D.op,
    a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  exact D.comm g h

instance opSubalgebra_isMulCommutative : IsMulCommutative ↥D.opSubalgebra :=
  Algebra.isMulCommutative_adjoin 𝒪 (fun a ha b hb _ => D.op_comm_of_mem a ha b hb)

open scoped IsMulCommutative

/-- **Hecke action of the free algebra.** The action of the free algebra on `V`
through the Hecke operators. -/
noncomputable def opAlgHom : D.FreeAlg →ₐ[𝒪] Module.End 𝒪 V :=
  (D.opSubalgebra.val).comp
    (MvPolynomial.aeval fun g => (⟨D.op g, Algebra.subset_adjoin
      (Set.mem_range_self g)⟩ : ↥D.opSubalgebra))

@[simp] theorem opAlgHom_X (g : D.Gen) :
    D.opAlgHom (MvPolynomial.X g) = D.op g := by
  simp [opAlgHom]

/-- **Free-algebra module structure.** The `FreeAlg`-module structure on `V`
given by the Hecke operators. -/
@[reducible] noncomputable def moduleFreeAlg : Module D.FreeAlg V :=
  Module.compHom V D.opAlgHom.toRingHom

attribute [local instance] moduleFreeAlg

/-- **Localized Hecke module.** The module `V` localized at the prime ideal
`mTheta`. It is a localization at a maximal ideal only when `mTheta` is maximal,
as in `finite_and_free_localizedModule_of_isMaximal`, or under the surjectivity
hypothesis of `finite_and_free_localizedModule`. -/
noncomputable abbrev ML : Type (max u v) := LocalizedModule D.mTheta.primeCompl V

/-- **Localization map.** The localization map from `V` to the localized
module. -/
noncomputable def toML : V →ₗ[D.FreeAlg] D.ML :=
  LocalizedModule.mkLinearMap D.mTheta.primeCompl V

theorem algebraMap_freeAlg_smul (r : 𝒪) (v : V) :
    (algebraMap 𝒪 D.FreeAlg r) • v = r • v := by
  change D.opAlgHom (algebraMap 𝒪 D.FreeAlg r) v = r • v
  rw [AlgHom.commutes]
  rfl

instance V_isScalarTower : IsScalarTower 𝒪 D.FreeAlg V :=
  ⟨fun r a v => by rw [Algebra.smul_def, mul_smul, algebraMap_freeAlg_smul]⟩

end HeckeData

/-- **Idempotent splitting.** An idempotent splitting of a commutative ring `B`
is a finite family of complete orthogonal idempotents, one for each maximal ideal
of `B`, with `e i` lying in every maximal ideal other than the `i`-th. -/
structure IdempotentSplitting (B : Type*) [CommRing B] where
  /-- The number of maximal ideals. -/
  n : ℕ
  /-- The idempotents. -/
  e : Fin n → B
  /-- The maximal ideals, enumerated. -/
  𝔪 : Fin n → Ideal B
  /-- The idempotents are complete and orthogonal. -/
  coi : CompleteOrthogonalIdempotents e
  /-- Each `𝔪 i` is maximal. -/
  isMaximal : ∀ i, (𝔪 i).IsMaximal
  /-- Every maximal ideal occurs. -/
  exists_eq : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I
  /-- `e i` lies in `𝔪 j` exactly when `i ≠ j`. -/
  mem_iff : ∀ i j, e i ∈ 𝔪 j ↔ i ≠ j

namespace IdempotentSplitting

variable {B : Type*} [CommRing B] (S : IdempotentSplitting B)

theorem notMem (i : Fin S.n) : S.e i ∉ S.𝔪 i :=
  fun h => ((S.mem_iff i i).mp h) rfl

theorem mem_of_ne {i j : Fin S.n} (h : i ≠ j) : S.e i ∈ S.𝔪 j :=
  (S.mem_iff i j).mpr h

theorem mem_of_isMaximal_of_ne (i : Fin S.n) (J : Ideal B) (hJ : J.IsMaximal)
    (hne : J ≠ S.𝔪 i) : S.e i ∈ J := by
  obtain ⟨j, rfl⟩ := S.exists_eq J hJ
  exact S.mem_of_ne fun h => hne (congrArg S.𝔪 h.symm)

theorem idem (i : Fin S.n) : IsIdempotentElem (S.e i) := S.coi.idem i

instance isMaximal_𝔪 (i : Fin S.n) : (S.𝔪 i).IsMaximal := S.isMaximal i

end IdempotentSplitting

section Corner

variable {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M] [Module B M]

/-- The corner submodule `e • M` cut out by an element `e` of `B`. -/
private def cornerSubmodule (e : B) : Submodule B M :=
  LinearMap.range (e • (LinearMap.id : M →ₗ[B] M))

/-- The map from `M` to its corner submodule. -/
private def toCorner (e : B) : M →ₗ[B] cornerSubmodule (M := M) e :=
  LinearMap.rangeRestrict (e • (LinearMap.id : M →ₗ[B] M))

@[simp] private theorem toCorner_apply (e : B) (v : M) :
    ((toCorner (M := M) e v : cornerSubmodule e) : M) = e • v := rfl

private theorem exists_mul_mul_eq_of_notMem {e : B} (he : IsIdempotentElem e)
    (𝔪 : Ideal B) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J)
    {s : B} (hs : s ∉ 𝔪) : ∃ t : B, t * s * e = e := by
  have htop : Ideal.span {s} ⊔ Ideal.span {1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1e : 1 - e ∈ J := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hsJ : s ∈ J := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hJ𝔪 : J ≠ 𝔪 := fun h => hs (h ▸ hsJ)
    have heJ : e ∈ J := hother J hJ hJ𝔪
    apply hJ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := J.add_mem heJ h1e
    rwa [add_sub_cancel] at this
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have key : t * s * e + u * ((1 - e) * e) = 1 * e := by
    have := congrArg (· * e) hab
    simpa only [add_mul, mul_assoc] using this
  rwa [h0, mul_zero, add_zero, one_mul] at key

private theorem isLocalizedModule_toCorner {e : B} (he : IsIdempotentElem e)
    (𝔪 : Ideal B) [𝔪.IsMaximal] (hem : e ∉ 𝔪)
    (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) :
    IsLocalizedModule 𝔪.primeCompl (toCorner (M := M) e) where
  map_units s := by
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem he 𝔪 hother s.2
    have hfix : ∀ z : cornerSubmodule (M := M) e, e • (z : M) = z := by
      intro z
      obtain ⟨z0, hz0⟩ := z.2
      rw [← hz0]
      simp [LinearMap.smul_apply, smul_smul, he.eq]
    have hact : ∀ z : cornerSubmodule (M := M) e,
        ((algebraMap B (Module.End B (cornerSubmodule (M := M) e)) (s : B) z :
          cornerSubmodule e) : M) = (s : B) • (z : M) := fun z => rfl
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hM : (s : B) • (x : M) = (s : B) • (y : M) := by
        rw [← hact x, ← hact y, hxy]
      calc (x : M) = e • (x : M) := (hfix x).symm
        _ = (t * s * e) • (x : M) := by rw [ht]
        _ = t • ((s : B) • (e • (x : M))) := by rw [mul_smul, mul_smul]
        _ = t • ((s : B) • (x : M)) := by rw [hfix x]
        _ = t • ((s : B) • (y : M)) := by rw [hM]
        _ = t • ((s : B) • (e • (y : M))) := by rw [hfix y]
        _ = (t * s * e) • (y : M) := by rw [mul_smul, mul_smul]
        _ = e • (y : M) := by rw [ht]
        _ = y := hfix y
    · intro y
      refine ⟨t • y, ?_⟩
      apply Subtype.ext
      rw [hact]
      change (s : B) • (t • (y : M)) = y
      calc (s : B) • (t • (y : M)) = ((s : B) * t) • (e • (y : M)) := by
            rw [hfix y, mul_smul]
        _ = ((s : B) * t * e) • (y : M) := (mul_smul _ _ _).symm
        _ = e • (y : M) := by rw [mul_comm (s : B) t, ht]
        _ = y := hfix y
  surj y := by
    refine ⟨((y : M), 1), ?_⟩
    apply Subtype.ext
    obtain ⟨y0, hy0⟩ := y.2
    simp only [one_smul, toCorner_apply]
    rw [← hy0]
    simp [LinearMap.smul_apply, smul_smul, he.eq]
  exists_of_eq {x₁ x₂} h := by
    refine ⟨⟨e, hem⟩, ?_⟩
    have := congrArg (fun z : cornerSubmodule (M := M) e => (z : M)) h
    simp only [toCorner_apply] at this
    exact this

end Corner

namespace IdempotentSplitting

variable {B : Type*} [CommRing B] (S : IdempotentSplitting B)

private theorem isLocalizedModule_toCorner_maximalIdeal (i : Fin S.n)
    {M : Type*} [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (toCorner (M := M) (S.e i)) :=
  isLocalizedModule_toCorner (S.idem i) (S.𝔪 i) (S.notMem i)
    (S.mem_of_isMaximal_of_ne i)

end IdempotentSplitting

/-- **Finite algebras over complete local rings split by idempotents.** A finite
algebra over a complete Noetherian local ring has an idempotent splitting: its
maximal ideals are finite in number and are separated by complete orthogonal
idempotents. -/
theorem nonempty_idempotentSplitting_of_finite (𝒪 : Type*) [CommRing 𝒪]
    [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (B : Type*) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B] :
    Nonempty (IdempotentSplitting B) := by
  classical
  obtain ⟨hfin, hbij, -, -⟩ :=
    Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
      (𝒪 := 𝒪) B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let Φ : B ≃+* ∀ I : MaximalSpectrum B, Localization.AtPrime I.asIdeal :=
    RingEquiv.ofBijective
      (RingHom.pi fun I : MaximalSpectrum B => algebraMap B (Localization.AtPrime I.asIdeal))
      hbij
  let e : MaximalSpectrum B → B := fun I => Φ.symm (Pi.single I 1)
  have hΦe : ∀ I, Φ (e I) = Pi.single I 1 := fun I => Φ.apply_symm_apply _
  have hloc : ∀ (I J : MaximalSpectrum B),
      algebraMap B (Localization.AtPrime J.asIdeal) (e I) =
        (Pi.single I 1 : ∀ i : MaximalSpectrum B, Localization.AtPrime i.asIdeal) J := by
    intro I J
    change Φ (e I) J = (Pi.single I 1 : ∀ i : MaximalSpectrum B,
      Localization.AtPrime i.asIdeal) J
    exact congrFun (hΦe I) J
  have hmem : ∀ I J : MaximalSpectrum B, e I ∈ J.asIdeal ↔ I ≠ J := by
    intro I J
    have h1 : algebraMap B (Localization.AtPrime J.asIdeal) (e I) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime J.asIdeal) ↔ e I ∈ J.asIdeal :=
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ J.asIdeal _
    rw [← h1, hloc]
    by_cases hIJ : I = J
    · subst hIJ
      simp
    · rw [Pi.single_eq_of_ne' hIJ]
      simp only [Ideal.zero_mem, true_iff]
      exact hIJ
  have hcoi : CompleteOrthogonalIdempotents e :=
    (CompleteOrthogonalIdempotents.single
      (fun I : MaximalSpectrum B => Localization.AtPrime I.asIdeal)).map
      Φ.symm.toRingHom
  let n := Fintype.card (MaximalSpectrum B)
  let σ : Fin n ≃ MaximalSpectrum B := (Fintype.equivFin (MaximalSpectrum B)).symm
  refine ⟨{ n := n, e := e ∘ σ, 𝔪 := fun i => (σ i).asIdeal,
            coi := CompleteOrthogonalIdempotents.equiv σ |>.mpr hcoi,
            isMaximal := fun i => (σ i).isMaximal,
            exists_eq := fun I hI => ⟨σ.symm ⟨I, hI⟩, by simp⟩,
            mem_iff := fun i j => (hmem (σ i) (σ j)).trans
              ⟨fun h hij => h (congrArg σ hij), fun h hij => h (σ.injective hij)⟩ }⟩

private theorem finite_cornerSubmodule {𝒪 : Type*} [CommRing 𝒪] {B : Type*}
    [CommRing B] [Algebra 𝒪 B] {V : Type*} [AddCommGroup V] [Module B V]
    [Module 𝒪 V] [IsScalarTower 𝒪 B V] (e : B) [Module.Finite 𝒪 V] :
    Module.Finite 𝒪 ↥(cornerSubmodule (M := V) e) := by
  have h : (cornerSubmodule (M := V) e).restrictScalars 𝒪
      = LinearMap.range ((e • (LinearMap.id : V →ₗ[B] V)).restrictScalars 𝒪) := by
    ext v
    simp only [Submodule.restrictScalars_mem, cornerSubmodule, LinearMap.mem_range,
      LinearMap.coe_restrictScalars]
  rw [show (Module.Finite 𝒪 ↥(cornerSubmodule (M := V) e))
      = Module.Finite 𝒪 ↥((cornerSubmodule (M := V) e).restrictScalars 𝒪) from rfl, h]
  exact Module.Finite.range _

private theorem free_cornerSubmodule {𝒪 : Type*} [CommRing 𝒪] {B : Type*}
    [CommRing B] [Algebra 𝒪 B] {V : Type*} [AddCommGroup V] [Module B V]
    [Module 𝒪 V] [IsScalarTower 𝒪 B V] (e : B) (he : IsIdempotentElem e)
    [IsLocalRing 𝒪] [Module.Finite 𝒪 V] [Module.Free 𝒪 V] :
    Module.Free 𝒪 ↥(cornerSubmodule (M := V) e) := by
  have hsplit : ((toCorner (M := V) e).restrictScalars 𝒪).comp
      ((cornerSubmodule (M := V) e).subtype.restrictScalars 𝒪) = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hy
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Submodule.coe_subtype, LinearMap.id_coe, id_eq, toCorner_apply]
    rw [← hy, smul_smul, he.eq]
  have : Module.Projective 𝒪 ↥(cornerSubmodule (M := V) e) :=
    Module.Projective.of_split
      ((cornerSubmodule (M := V) e).subtype.restrictScalars 𝒪)
      ((toCorner (M := V) e).restrictScalars 𝒪) hsplit
  have : Module.Finite 𝒪 ↥(cornerSubmodule (M := V) e) := finite_cornerSubmodule e
  exact Module.free_of_flat_of_isLocalRing

private theorem isLocalizedModule_comap_primeCompl {Λ B : Type*} [CommRing Λ]
    [CommRing B] [Algebra Λ B] (hπ : Function.Surjective (algebraMap Λ B))
    (𝔭 : Ideal B) [𝔭.IsPrime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] [Module Λ M] [Module Λ N] [IsScalarTower Λ B M]
    [IsScalarTower Λ B N] (f : M →ₗ[B] N) [IsLocalizedModule 𝔭.primeCompl f] :
    IsLocalizedModule (𝔭.comap (algebraMap Λ B)).primeCompl (f.restrictScalars Λ) := by
  have key : Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl
      = 𝔭.primeCompl := by
    ext b
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ht
    · intro hb; obtain ⟨t, rfl⟩ := hπ b; exact ⟨t, hb, rfl⟩
  have : IsLocalizedModule
      (Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl) f := by
    rw [key]; infer_instance
  exact IsLocalizedModule.restrictScalars _ f

namespace HeckeData

attribute [local instance] moduleFreeAlg

private theorem thetaTilde_surjective {𝒪 : Type*} [CommRing 𝒪] {V : Type*}
    [AddCommGroup V] [Module 𝒪 V] {k : Type*} [Field k] [Algebra 𝒪 k]
    (hk : Function.Surjective (algebraMap 𝒪 k)) (D : HeckeData 𝒪 V k) :
    Function.Surjective D.thetaTilde := by
  intro c
  obtain ⟨r, hr⟩ := hk c
  exact ⟨algebraMap 𝒪 D.FreeAlg r, by rw [AlgHom.commutes]; exact hr⟩

/-- **Localized Hecke modules are finite and free.** Let `V` be a finite module
over a complete Noetherian local ring `𝒪`, and suppose that the eigenvalue ideal
`mTheta` is maximal. Then the localization `ML` of `V` at `mTheta` is finite over
`𝒪`, and it is free over `𝒪` when `V` is. -/
theorem finite_and_free_localizedModule_of_isMaximal {𝒪 : Type*} [CommRing 𝒪]
    [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type*} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type*} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k) [h𝔭 : D.mTheta.IsMaximal] :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) := by
  classical
  set I : Ideal D.FreeAlg := RingHom.ker D.opAlgHom.toRingHom with hI
  let φ : (D.FreeAlg ⧸ I) →ₐ[𝒪] Module.End 𝒪 V :=
    Ideal.Quotient.liftₐ I D.opAlgHom fun a ha => (RingHom.mem_ker).mp ha
  have hφ_inj : Function.Injective φ := fun x y hxy =>
    RingHom.lift_injective_of_ker_le_ideal I (f := D.opAlgHom.toRingHom)
      (fun a ha => (RingHom.mem_ker).mp ha) le_rfl hxy
  have hφ_mk : ∀ a : D.FreeAlg, φ (Ideal.Quotient.mk I a) = D.opAlgHom a :=
    fun a => Ideal.Quotient.lift_mk I _ _
  have : IsNoetherian 𝒪 (D.FreeAlg ⧸ I) := isNoetherian_of_injective φ.toLinearMap hφ_inj
  let : Module (D.FreeAlg ⧸ I) V := Module.compHom V φ.toRingHom
  have hsmul : ∀ (b : D.FreeAlg ⧸ I) (v : V), b • v = φ b v := fun _ _ => rfl
  have : IsScalarTower D.FreeAlg (D.FreeAlg ⧸ I) V :=
    ⟨fun a b v => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hab : a • Ideal.Quotient.mk I b = Ideal.Quotient.mk I (a * b) := rfl
      rw [hab]
      simp only [hsmul]
      rw [hφ_mk, hφ_mk, map_mul, mul_apply_eq_comp]
      rfl⟩
  have : IsScalarTower 𝒪 (D.FreeAlg ⧸ I) V :=
    ⟨fun r b v => by rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have hmk : Function.Surjective (algebraMap D.FreeAlg (D.FreeAlg ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective h𝔭 with htop | hmax
  · have hsup : (1 : D.FreeAlg) ∈ D.mTheta ⊔ I := by
      have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective D.mTheta
      rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
      rw [← h]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hsup
    obtain ⟨p, hp, s, hs, hps⟩ := hsup
    have hs𝔭 : s ∉ D.mTheta := fun h =>
      h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr (hps ▸ D.mTheta.add_mem hp h))
    have hsV : ∀ v : V, s • v = 0 := fun v => by
      change D.opAlgHom s v = 0
      rw [show D.opAlgHom s = 0 from (RingHom.mem_ker).mp hs]
      rfl
    have : Subsingleton D.ML := LocalizedModule.subsingleton_iff.mpr fun v => ⟨s, hs𝔭, hsV v⟩
    have : Finite D.ML := Finite.of_subsingleton
    exact ⟨inferInstance, fun _ => inferInstance⟩
  · have hcomap : (D.mTheta.map (Ideal.Quotient.mk I)).comap
        (algebraMap D.FreeAlg (D.FreeAlg ⧸ I)) = D.mTheta := by
      have hne := Ideal.comap_ne_top (Ideal.Quotient.mk I) hmax.ne_top
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hne
      rw [Ideal.Quotient.algebraMap_eq,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact (h𝔭.eq_of_le hne le_sup_left).symm
    obtain ⟨S⟩ := nonempty_idempotentSplitting_of_finite 𝒪 (D.FreeAlg ⧸ I)
    obtain ⟨i, hi⟩ := S.exists_eq _ hmax
    rw [← hi] at hcomap
    have h₁ := S.isLocalizedModule_toCorner_maximalIdeal i (M := V)
    have h₂ := isLocalizedModule_comap_primeCompl hmk (S.𝔪 i)
      (toCorner (M := V) (S.e i))
    have h₃ : IsLocalizedModule D.mTheta.primeCompl
        ((toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg) := by
      convert h₂ using 3
      exact hcomap.symm
    have : IsScalarTower 𝒪 D.FreeAlg ↥(cornerSubmodule (M := V) (S.e i)) :=
      ⟨fun r a x => Subtype.ext (smul_assoc r a (x : V))⟩
    let e : D.ML ≃ₗ[𝒪] ↥(cornerSubmodule (M := V) (S.e i)) :=
      (IsLocalizedModule.iso D.mTheta.primeCompl
        ((toCorner (M := V) (S.e i)).restrictScalars D.FreeAlg)).restrictScalars 𝒪
    have := finite_cornerSubmodule (𝒪 := 𝒪) (V := V) (S.e i)
    refine ⟨Module.Finite.equiv e.symm, fun hV => ?_⟩
    have := hV
    have := free_cornerSubmodule (𝒪 := 𝒪) (V := V) (S.e i) (S.idem i)
    exact Module.Free.of_equiv e.symm

/-- **Localized Hecke modules with residue-field eigenvalues are finite and free.**
Let `V` be a finite module over a complete Noetherian local ring `𝒪`, and let
`algebraMap 𝒪 k` be surjective (`hk`), so that `k` is the residue field of `𝒪`
and `mTheta` is a maximal ideal. Then the localization `ML` of `V` at `mTheta` is
finite over `𝒪`, and it is free over `𝒪` when `V` is. -/
theorem finite_and_free_localizedModule {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type*} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type*} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) := by
  have : D.mTheta.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective D.thetaTilde.toRingHom (thetaTilde_surjective hk D)
  exact finite_and_free_localizedModule_of_isMaximal D

end HeckeData
