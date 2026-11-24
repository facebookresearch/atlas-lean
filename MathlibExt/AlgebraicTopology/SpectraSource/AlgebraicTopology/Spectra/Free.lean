/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/Free.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.AddBasepoint
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SymmetricSpectrum
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Free.Basic

/-!
# Free symmetric spectra

Evaluation of a symmetric spectrum at level `n` has a left adjoint `F_n`.
First freely place a pointed simplicial set in a symmetric sequence at level `n`,
using the coproduct indexed by bijections out of `Fin n`, and then take the free
module over the sphere sequence. Thus the permutation actions and the iterated
structure maps are those of the native sphere-module carrier.

The first step is the free symmetric sequence `G_n K = (SymmetricSequence.free n).obj K`, left
adjoint to evaluation of symmetric sequences, with generator `SymmetricSequence.freeι n K`. It is
the point in every level other than `n`. The generator `K ⟶ (G₀ K)₀` is an isomorphism, and
`G₀ S⁰` is the unit of the Day convolution (`SymmetricSequence.freeZeroUnitIso`).

The adjunction is obtained by composing Mathlib's `evaluationAdjunctionRight`,
the equivalence between Day functors and ordinary functors, and the free-module
adjunction. Precomposing with adjoining a disjoint basepoint gives the adjunction
`SymmetricSpectrum.freeAddBasepointAdjunction` between unpointed simplicial sets and level `n`.
These are point-set constructions, without a model structure or a
claim about derived mapping spaces. Free spectra supply the cells for level and
stable model structures.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc.
  13 (2000), Section 2.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

open scoped DayFunctor

namespace SymmetricSequence

/-- The free symmetric sequence `G_n K` on a pointed simplicial set `K` in level `n`: its level
`m` is the wedge of copies of `K` indexed by the bijections `Fin n ≃ Fin m`. Thus it is `K` with
the free based `Σ_n`-action in level `n`, and the point in every other level. -/
noncomputable abbrev free (n : ℕ) : PointedSSet.{0} ⥤ SymmetricSequence.{0} :=
  evaluationLeftAdjoint PointedSSet.{0} (FiniteBijection.mk n) ⋙
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse

/-- The free symmetric sequence in level `n` is left adjoint to evaluation at level `n`. -/
noncomputable def freeEvaluationAdjunction (n : ℕ) :
    free n ⊣ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
      (evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk n) :=
  (evaluationAdjunctionRight PointedSSet.{0} (FiniteBijection.mk n)).comp
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).symm.toAdjunction

/-- The universal generator `K ⟶ (G_n K)_n` of the free symmetric sequence: the summand of the
identity bijection. -/
noncomputable def freeι (n : ℕ) (K : PointedSSet.{0}) :
    K ⟶ ((free n).obj K).functor.obj (FiniteBijection.mk n) :=
  Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) (𝟙 _)

/-- The universal generator of the free symmetric sequence is natural in the pointed simplicial
set. -/
@[reassoc (attr := simp)]
lemma freeι_naturality (n : ℕ) {K L : PointedSSet.{0}} (f : K ⟶ L) :
    f ≫ freeι n L =
      freeι n K ≫
        ((free n).map f).natTrans.app (FiniteBijection.mk n) :=
  (Limits.Sigma.ι_comp_desc (fun h ↦ f ≫ Limits.Sigma.ι (fun _ ↦ L) h) (𝟙 _)).symm

/-- The unit of the free symmetric sequence adjunction is the universal generator. -/
@[simp]
lemma freeEvaluationAdjunction_unit_app (n : ℕ) (K : PointedSSet.{0}) :
    (freeEvaluationAdjunction n).unit.app K = freeι n K := by
  simp only [freeEvaluationAdjunction, freeι,
    Adjunction.comp_unit_app, evaluationAdjunctionRight_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, Equivalence.counitInv,
    DayFunctor.equiv_counitIso_inv_app]
  exact Category.comp_id _

/-- A map out of the free symmetric sequence, obtained by extending a map from `K` into level
`n`, agrees with the original map on the generator. -/
@[reassoc]
lemma freeι_comp_homEquiv_symm (n : ℕ) {K : PointedSSet.{0}}
    {Y : SymmetricSequence.{0}} (g : K ⟶ Y.functor.obj (FiniteBijection.mk n)) :
    freeι n K ≫
      (((freeEvaluationAdjunction n).homEquiv K Y).symm g).natTrans.app
        (FiniteBijection.mk n) = g := by
  have h := ((freeEvaluationAdjunction n).homEquiv K Y).apply_symm_apply g
  rw [Adjunction.homEquiv_unit, freeEvaluationAdjunction_unit_app] at h
  exact h

/-- The free symmetric sequence `G_n K` is the point in every level `m ≠ n`: there is no bijection
`Fin n ≃ Fin m`. -/
noncomputable def isInitialFreeObj (K : PointedSSet.{0}) {n m : ℕ}
    (h : m ≠ n) :
    Limits.IsInitial (((free n).obj K).functor.obj (FiniteBijection.mk m)) :=
  have : IsEmpty (FiniteBijection.mk n ⟶ FiniteBijection.mk m) :=
    ⟨fun f ↦ h (congrArg FiniteBijection.len (FiniteBijection.eq_of_hom f)).symm⟩
  (Limits.isColimitEquivIsInitialOfIsEmpty _ _) (Limits.colimit.isColimit _)

/-- In level zero the free symmetric sequence is the pointed simplicial set itself: the generator
`K ⟶ (G₀ K)₀` is an isomorphism, as `Fin 0` has a single bijection. -/
instance isIso_freeι_zero (K : PointedSSet.{0}) :
    IsIso (freeι 0 K) := by
  let _ : Unique (FiniteBijection.mk 0 ⟶ FiniteBijection.mk 0) :=
    ⟨⟨𝟙 _⟩, fun _ ↦ FiniteBijection.hom_ext fun i ↦ i.elim0⟩
  -- `freeι 0 K` includes the summand of `𝟙 _ = default` into a coproduct with a single summand.
  rw [freeι, Subsingleton.elim (𝟙 (FiniteBijection.mk 0)) default,
    ← Limits.coproductUniqueIso_inv]
  exact (Limits.coproductUniqueIso _).isIso_inv

/-- The map `G₀ S⁰ ⟶ 𝟙` adjoint to the identification `S⁰ ≅ 𝟙₀` of level zero of the unit. -/
private noncomputable def freeZeroUnitHom :
    (free 0).obj (𝟙_ PointedSSet.{0}) ⟶ 𝟙_ SymmetricSequence.{0} :=
  ((freeEvaluationAdjunction 0).homEquiv _ _).symm (DayFunctor.ν FiniteBijection PointedSSet.{0})

private lemma freeι_comp_freeZeroUnitHom :
    freeι 0 (𝟙_ PointedSSet.{0}) ≫ freeZeroUnitHom.natTrans.app (FiniteBijection.mk 0) =
      DayFunctor.ν FiniteBijection PointedSSet.{0} :=
  freeι_comp_homEquiv_symm 0 _

/-- The map `G₀ S⁰ ⟶ 𝟙` is an isomorphism: in level zero it is `S⁰ ≅ 𝟙₀` after the generator, and
in positive levels both symmetric sequences are the point. -/
private lemma isIso_freeZeroUnitHom : IsIso freeZeroUnitHom := by
  have hn : ∀ c : FiniteBijection, IsIso (freeZeroUnitHom.natTrans.app c) := by
    rintro ⟨_ | m⟩
    · have : IsIso (freeι 0 (𝟙_ PointedSSet.{0}) ≫
          freeZeroUnitHom.natTrans.app (FiniteBijection.mk 0)) := by
        rw [freeι_comp_freeZeroUnitHom]
        infer_instance
      exact IsIso.of_isIso_comp_left (freeι 0 (𝟙_ PointedSSet.{0})) _
    · exact Limits.isIso_of_isInitial (isInitialFreeObj _ (Nat.succ_ne_zero m))
        (isInitialUnitObj m) _
  have : IsIso ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
      freeZeroUnitHom) := by
    rw [DayFunctor.equiv_functor_map]
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hn
  exact isIso_of_reflects_iso _ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor

/-- The free symmetric sequence `G₀ S⁰` on the unit `S⁰` in level zero is the unit of the Day
convolution. On the generator it is the identification `S⁰ ≅ 𝟙₀` of level zero of the unit
(`freeι_comp_freeZeroUnitIso_hom`). -/
noncomputable def freeZeroUnitIso : (free 0).obj (𝟙_ PointedSSet.{0}) ≅ 𝟙_ SymmetricSequence.{0} :=
  have := isIso_freeZeroUnitHom
  asIso freeZeroUnitHom

/-- On the generator of `G₀ S⁰`, the isomorphism `G₀ S⁰ ≅ 𝟙` is the identification `S⁰ ≅ 𝟙₀`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_freeZeroUnitIso_hom :
    freeι 0 (𝟙_ PointedSSet.{0}) ≫ freeZeroUnitIso.hom.natTrans.app (FiniteBijection.mk 0) =
      DayFunctor.ν FiniteBijection PointedSSet.{0} := by
  rw [freeZeroUnitIso, asIso_hom, freeι_comp_freeZeroUnitHom]

end SymmetricSequence

namespace SymmetricSpectrum

/-- Evaluation of a sphere module at the standard finite set `Fin n`. -/
noncomputable abbrev evaluation (n : ℕ) : SymmetricSpectrum ⥤ PointedSSet.{0} where
  obj E := E.X.functor.obj (FiniteBijection.mk n)
  map f := f.hom.natTrans.app (FiniteBijection.mk n)

/-- The free symmetric spectrum `F_n K`: freely adjoin the symmetric action in
level `n`, then freely adjoin the sphere action. -/
-- Reducibility identifies the target of freeι with the concrete sphere-module level
-- in freeι_eq, so its identity-bijection formula needs no equality transports.
noncomputable abbrev free (n : ℕ) : PointedSSet.{0} ⥤ SymmetricSpectrum :=
  SymmetricSequence.free n ⋙ freeMod SymmetricSequence.sphere

/-- The free spectrum in level `n` is left adjoint to level-`n` evaluation. -/
noncomputable def freeEvaluationAdjunction (n : ℕ) : free n ⊣ evaluation n :=
  (SymmetricSequence.freeEvaluationAdjunction n).comp (freeModAdjunction SymmetricSequence.sphere)

/-- The free spectrum `F_n (K₊)` on a simplicial set with a disjoint basepoint is left adjoint to
the underlying simplicial set of level `n`. -/
noncomputable def freeAddBasepointAdjunction (n : ℕ) :
    PointedSSet.addBasepoint ⋙ free n ⊣ evaluation n ⋙ PointedSSet.forgetBasepoint :=
  PointedSSet.addBasepointForgetAdjunction.comp (freeEvaluationAdjunction n)

/-- The universal generator of `F_n K` in level `n`. -/
noncomputable def freeι (n : ℕ) (K : PointedSSet.{0}) :
    K ⟶ (evaluation n).obj ((free n).obj K) :=
  (freeEvaluationAdjunction n).unit.app K

/-- The spectral adjunction unit is the universal generator. -/
@[simp]
lemma freeEvaluationAdjunction_unit_app (n : ℕ) (K : PointedSSet.{0}) :
    (freeEvaluationAdjunction n).unit.app K = freeι n K := (rfl)

/-- The generator is the generator of the free symmetric sequence `G_n K` followed by the
sphere-unit inclusion. -/
lemma freeι_eq (n : ℕ) (K : PointedSSet.{0}) :
    freeι n K = SymmetricSequence.freeι n K ≫
      (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj K)).natTrans.app
        (FiniteBijection.mk n) := by
  simp only [freeι, freeEvaluationAdjunction, Adjunction.comp_unit_app,
    SymmetricSequence.freeEvaluationAdjunction_unit_app, freeModAdjunction_unit_app]
  -- The forgetful functor to ordinary functors acts on a map of Day functors by its components.
  rfl

/-- Extension of a level-`n` map to a spectrum map from `F_n K`. -/
noncomputable def freeDesc {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ (evaluation n).obj E) : (free n).obj K ⟶ E :=
  ((freeEvaluationAdjunction n).homEquiv K E).symm f

/-- The inverse adjunction bijection extends a map from the generating level. -/
@[simp]
lemma freeEvaluationAdjunction_homEquiv_symm_apply {n : ℕ} {K : PointedSSet.{0}}
    (E : SymmetricSpectrum) (f : K ⟶ (evaluation n).obj E) :
    dsimp% ((freeEvaluationAdjunction n).homEquiv K E).symm f = freeDesc E f := (rfl)

/-- The spectral adjunction counit extends the identity on the evaluated level. -/
@[simp]
lemma freeEvaluationAdjunction_counit_app (n : ℕ) (E : SymmetricSpectrum) :
    (freeEvaluationAdjunction n).counit.app E = freeDesc E (𝟙 ((evaluation n).obj E)) := by
  rw [← Adjunction.homEquiv_symm_id, freeEvaluationAdjunction_homEquiv_symm_apply]

/-- A free-spectrum extension agrees with the original map on the generator. -/
@[simp↓, reassoc (attr := simp)]
lemma freeι_desc {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ (evaluation n).obj E) :
    dsimp% freeι n K ≫ (evaluation n).map (freeDesc E f) = f := by
  simpa only [freeι, freeDesc, Adjunction.homEquiv_unit] using
    ((freeEvaluationAdjunction n).homEquiv K E).apply_symm_apply f

/-- Every map from a free spectrum is recovered by extension of its generator. -/
@[simp↓]
lemma freeDesc_ι {n : ℕ} {K : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : (free n).obj K ⟶ E) :
    dsimp% freeDesc E (freeι n K ≫ (evaluation n).map f) = f := by
  simpa only [freeι, freeDesc, Adjunction.homEquiv_unit] using
    ((freeEvaluationAdjunction n).homEquiv K E).symm_apply_apply f

/-- The universal generator is natural in the pointed simplicial set. -/
@[reassoc (attr := simp)]
lemma freeι_naturality {n : ℕ} {K L : PointedSSet.{0}} (f : K ⟶ L) :
    f ≫ freeι n L = freeι n K ≫ (evaluation n).map ((free n).map f) := by
  simpa only [freeι, Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] using
    (freeEvaluationAdjunction n).unit.naturality f

/-- Extension from a free spectrum commutes with post-composition. -/
@[simp, reassoc]
lemma freeDesc_comp {n : ℕ} {K : PointedSSet.{0}} {E E' : SymmetricSpectrum}
    (f : K ⟶ (evaluation n).obj E) (g : E ⟶ E') :
    freeDesc E f ≫ g = freeDesc E' (f ≫ (evaluation n).map g) := by
  simpa only [freeDesc] using
    ((freeEvaluationAdjunction n).homEquiv_naturality_right_symm f g).symm

/-- Extension from a free spectrum commutes with pre-composition on generators. -/
@[simp, reassoc]
lemma free_map_freeDesc {n : ℕ} {K L : PointedSSet.{0}} (E : SymmetricSpectrum)
    (f : K ⟶ L) (g : L ⟶ (evaluation n).obj E) :
    dsimp% (free n).map f ≫ freeDesc E g = freeDesc E (f ≫ g) := by
  simpa only [freeDesc] using
    (dsimp% ((freeEvaluationAdjunction n).homEquiv_naturality_left_symm f g).symm)

/-- Maps out of a free spectrum are determined by the universal generator. -/
@[ext]
lemma free_hom_ext {n : ℕ} {K : PointedSSet.{0}} {E : SymmetricSpectrum}
    {f g : (free n).obj K ⟶ E}
    (h : freeι n K ≫ (evaluation n).map f = freeι n K ≫ (evaluation n).map g) :
    f = g := by
  apply ((freeEvaluationAdjunction n).homEquiv K E).injective
  simpa only [Adjunction.homEquiv_unit, freeι] using h

end SymmetricSpectrum

end MathlibExt.SpectraSource
