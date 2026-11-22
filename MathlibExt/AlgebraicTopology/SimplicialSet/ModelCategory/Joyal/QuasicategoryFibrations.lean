/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunctionRestriction
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingFibrantCodomain
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization
public import MathlibExt.AlgebraicTopology.Quasicategory.CoherentEndpointLifting
public import MathlibExt.AlgebraicTopology.Quasicategory.FunctionEquivalenceLifting
public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLiftingIsofibration
public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystemEndpoints
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEquivalences

/-!
# Genuine categorical fibrations over quasicategories

The native genuine categorical right class is exactly the class of inner
fibrations with strict equivalence-edge lifting when the codomain is a
quasicategory. The source quasicategory is inferred. The equivalent criteria
use the original coherent endpoint lifting property and the actual ordinary
homotopy-category functor. The actual finite-J genuine/naive class bridge and
its derived strict naive criterion are also included.

For the converse criterion, extend the original top map through weak-mono
restriction, form the literal function-pullback vertex for the original
square, and lift the identity edge through its first projection with fixed
endpoints. Its homotopy-category functor reflects equivalences. Canonical
strict Leibniz lifting then solves both original square equations.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial
universe u

namespace SSet

/-- The actual genuine and finite-interval naive right classes agree over a quasicategory. -/
public theorem joyalInterval.categoricalFibrations_iff_auxiliaryNaiveFibrations {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] :
    SSet.categoricalFibrations p ↔ SSet.joyalInterval.auxiliaryNaiveFibrations p := by
  let : HasFactorization SSet.joyalInterval.auxiliaryAnodyneExtensions
      SSet.joyalInterval.auxiliaryAnodyneExtensions.rlp := by
    change HasFactorization SSet.joyalInterval.auxiliaryAnodyneExtensions
      SSet.joyalInterval.auxiliaryNaiveFibrations
    infer_instance
  have hY : SSet.joyalInterval.auxiliaryAnodyneExtensions.naiveFibrantObjects Y := by
    change SSet.joyalInterval.auxiliaryNaiveFibrantObjects Y
    exact (SSet.joyalInterval.auxiliaryNaiveFibrantObjects_iff Y).mpr inferInstance
  have h := HomotopicalAlgebra.Precylinder.IsAnodyneSystem.testingFibrations_iff_naiveFibrations_of_naiveFibrant
      SSet.joyalInterval.productPrecylinder SSet.joyalInterval.auxiliaryAnodyneExtensions p hY
  rw [SSet.joyalInterval.productPrecylinder.testingFibrations_iff
    SSet.joyalInterval.auxiliaryAnodyneExtensions p] at h
  rw [SSet.categoricalFibrations.mem_iff]
  simpa only [SSet.joyalInterval.testingEquivalences_eq_categoricalEquivalences,
    SSet.joyalInterval.auxiliaryNaiveFibrations] using h

private lemma rlp_pre_of_mono_categoricalEquivalence {A B Q : SSet.{u}}
    (i : A ⟶ B) [Mono i] (hi : SSet.categoricalEquivalences i)
    [SSet.Quasicategory Q] :
    (monomorphisms SSet.{u}).rlp ((pre i).app Q) := by
  have h := (SSet.categoricalFibrations_and_categoricalEquivalences_iff _).mp
    (SSet.categoricalFibrations_and_categoricalEquivalences_pre_app_of_mono i hi Q)
  rwa [← SSet.rlp_monomorphisms] at h

private lemma rlp_fst_of_mono_categoricalEquivalence {A B X Y : SSet.{u}} {r : A ⟶ B} {p : X ⟶ Y}
    [Mono r] (hr : SSet.categoricalEquivalences r) [SSet.Quasicategory Y]
    (sq : MonoidalClosed.internalHom.PullbackObjObj r p) :
    (monomorphisms SSet.{u}).rlp sq.fst := by
  exact (monomorphisms SSet.{u}).rlp.of_isPullback sq.isPullback.flip
    (rlp_pre_of_mono_categoricalEquivalence r hr)

private lemma square_lifting_of_strict_packet
    {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) {p : X ⟶ Y}
    [SSet.Quasicategory X] [SSet.Quasicategory Y]
    (sq : MonoidalClosed.internalHom.PullbackObjObj i p)
    [SSet.HasStrictEquivalenceLifting sq.π] : HasLiftingProperty i p := by
  constructor
  intro a b hab
  let fst : sq.pt ⟶ (ihom A).obj X := sq.fst
  let snd : sq.pt ⟶ (ihom B).obj Y := sq.snd
  let pi : (ihom B).obj X ⟶ sq.pt := sq.π
  have hpiA : pi ≫ fst = (pre i).app X := sq.π_fst
  have hpiB : pi ≫ snd = (ihom B).map p := sq.π_snd
  let av := SSet.ihomVertexEquiv A X a
  let bv := SSet.ihomVertexEquiv B Y b
  have hcompat : ((ihom A).map p).app (op ⦋0⦌) av =
      ((pre i).app Y).app (op ⦋0⦌) bv := by
    dsimp only [av, bv]
    rw [SSet.ihomVertexEquiv_ihom_map, SSet.ihomVertexEquiv_pre_app]
    exact congrArg (SSet.ihomVertexEquiv A Y) hab.w
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)
  obtain ⟨w, hwA, hwB⟩ := Types.exists_of_isPullback
    (sq.isPullback.map E) av bv hcompat
  change fst.app (op ⦋0⦌) w = av at hwA
  change snd.app (op ⦋0⦌) w = bv at hwB
  have hRX : SSet.modelCategoryQuillen.I.rlp ((pre i).app X) := by
    rw [← SSet.rlp_monomorphisms]
    exact rlp_pre_of_mono_categoricalEquivalence i hi
  obtain ⟨u₀, hu₀⟩ := SSet.exists_vertex_lift_of_rlp_I hRX av
  have hsrc : fst.app (op ⦋0⦌) (pi.app (op ⦋0⦌) u₀) = av := by
    change (pi ≫ fst).app (op ⦋0⦌) u₀ = av
    rw [hpiA]
    exact hu₀
  have hRF : (monomorphisms SSet.{u}).rlp fst := rlp_fst_of_mono_categoricalEquivalence hi sq
  have hFI : SSet.modelCategoryQuillen.I.rlp fst := by
    rwa [← SSet.rlp_monomorphisms]
  obtain ⟨e, he⟩ := SSet.exists_edge_lift_of_rlp_I hFI hsrc hwA (SSet.Edge.id av)
  have hid : (SSet.Edge.id av).IsEquivalence := by
    rw [SSet.Edge.isEquivalence_iff, SSet.Edge.toHoHom_id]
    infer_instance
  have hmap : (e.map fst).IsEquivalence := hid.of_edge_eq he.symm
  let : (SSet.mapHomotopyCategory fst).IsEquivalence :=
    SSet.mapHomotopyCategory_isEquivalence_of_rlp_monomorphisms hRF
  let : IsIso ((SSet.mapHomotopyCategory fst).map e.toHoHom) := by
    rw [← SSet.Edge.toHoHom_map]
    exact (SSet.Edge.isEquivalence_iff _).mp hmap
  let : IsIso e.toHoHom := isIso_of_reflects_iso e.toHoHom (SSet.mapHomotopyCategory fst)
  have heq : e.IsEquivalence := (SSet.Edge.isEquivalence_iff _).mpr inferInstance
  let : SSet.HasStrictEquivalenceLifting pi := inferInstanceAs
    (SSet.HasStrictEquivalenceLifting sq.π)
  obtain ⟨u₁, hu₁, _, _, _⟩ := SSet.HasStrictEquivalenceLifting.exists_lift (p := pi) e heq
  let b₁ : B ⟶ X := (SSet.ihomVertexEquiv B X).symm u₁
  refine ⟨b₁, ?_, ?_⟩
  · apply (SSet.ihomVertexEquiv A X).injective
    dsimp only [b₁]
    rw [← SSet.ihomVertexEquiv_pre_app, Equiv.apply_symm_apply, ← hpiA]
    change fst.app (op ⦋0⦌) (pi.app (op ⦋0⦌) u₁) = av
    exact (congrArg (fst.app (op ⦋0⦌)) hu₁).trans hwA
  · apply (SSet.ihomVertexEquiv B Y).injective
    dsimp only [b₁]
    rw [← SSet.ihomVertexEquiv_ihom_map, Equiv.apply_symm_apply, ← hpiB]
    change snd.app (op ⦋0⦌) (pi.app (op ⦋0⦌) u₁) = bv
    exact (congrArg (snd.app (op ⦋0⦌)) hu₁).trans hwB

private lemma unitPoint_mem_auxiliary (ε : Fin 2) :
    SSet.joyalInterval.auxiliaryAnodyneExtensions.{u}
      (SSet.joyalInterval.unitPoint.{u} ε) := by
  let An : MorphismProperty SSet.{u} := SSet.joyalInterval.auxiliaryAnodyneExtensions
  have hEq : An.rlp.llp = An :=
    HomotopicalAlgebra.Precylinder.IsAnodyneSystem.llp_rlp_eq
      SSet.joyalInterval.productPrecylinder An
  let a : (𝟙_ SSet.{u}) ⟶ (SSet.joyalInterval.{u} ⊗ 𝟙_ SSet.{u}) :=
    (SSet.joyalInterval.productPrecylinder.app (𝟙_ SSet.{u})).endpoint ε
  have ha : a = (λ_ (𝟙_ SSet.{u})).inv ≫
      SSet.joyalInterval.unitPoint ε ▷ (𝟙_ SSet.{u}) :=
    SSet.joyalInterval.productPrecylinder_endpoint_unitor _ ε
  have hAn : An.rlp.llp a :=
    (congrArg (fun Q : MorphismProperty SSet.{u} => Q a) hEq).mpr
      (HomotopicalAlgebra.Precylinder.IsAnodyneSystem.endpoint_mem_anodyne
        SSet.joyalInterval.productPrecylinder An (𝟙_ SSet.{u}) ε)
  have heq : a ≫ (ρ_ SSet.joyalInterval.{u}).hom = SSet.joyalInterval.unitPoint ε := by
    rw [ha, Category.assoc, rightUnitor_naturality, ← unitors_equal]
    simp
  have hrho : An.rlp.llp (ρ_ SSet.joyalInterval.{u}).hom :=
    MorphismProperty.llp_of_isIso _ _
  have h := An.rlp.llp.comp_mem
    a (ρ_ SSet.joyalInterval.{u}).hom hAn hrho
  rw [heq] at h
  exact (congrArg (fun Q : MorphismProperty SSet.{u} =>
    Q (SSet.joyalInterval.unitPoint ε)) hEq).mp h

private lemma inner_strict_of_genuine {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] (hp : SSet.categoricalFibrations p) :
    SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p := by
  have hn : SSet.joyalInterval.auxiliaryNaiveFibrations p :=
    (joyalInterval.categoricalFibrations_iff_auxiliaryNaiveFibrations p).mp hp
  refine ⟨(SSet.joyalInterval.auxiliaryNaiveFibrations_iff p).mp hn |>.1, ?_⟩
  constructor
  intro x₀ y₁ g hg
  obtain ⟨t, ht⟩ := hg.exists_joyalInterval_extension
  let U : (𝟙_ SSet.{u}) ≅ (Δ[0] : SSet.{u}) :=
    SemiCartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
      SSet.stdSimplex.isTerminalObj₀
  let a : (𝟙_ SSet.{u}) ⟶ X := U.hom ≫ SSet.yonedaEquiv.symm x₀
  have hcompat : a ≫ p = SSet.joyalInterval.unitPoint 0 ≫ t := by
    have ht₀ : SSet.joyalInterval.endpoint 0 ≫ t =
        SSet.yonedaEquiv.symm (p.app (op ⦋0⦌) x₀) := by
      rw [SSet.joyalInterval.endpoint_zero, Category.assoc, ht,
        SSet.Edge.δ_one_yonedaEquiv_symm]
    dsimp only [a, SSet.joyalInterval.unitPoint]
    simp only [Category.assoc, ht₀, SSet.yonedaEquiv_symm_comp]
    rfl
  let sq : CommSq a (SSet.joyalInterval.unitPoint 0) p t := ⟨hcompat⟩
  have hLP : HasLiftingProperty (SSet.joyalInterval.unitPoint 0) p :=
    hn _ (unitPoint_mem_auxiliary 0)
  let : sq.HasLift := hLP.sq_hasLift sq
  let l : SSet.joyalInterval.{u} ⟶ X := sq.lift
  have hs : SSet.joyalInterval.endpoint 0 ≫ l = SSet.yonedaEquiv.symm x₀ := by
    apply (cancel_epi U.hom).mp
    simpa only [a, SSet.joyalInterval.unitPoint, U, l, Category.assoc] using sq.fac_left
  let raw : X _⦋1⦌ := SSet.yonedaEquiv (SSet.joyalInterval.forward ≫ l)
  have hsrc : X.δ 1 raw = x₀ := by
    dsimp only [raw]
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp]
    change SSet.yonedaEquiv (SSet.joyalInterval.endpoint 0 ≫ l) = x₀
    rw [hs, Equiv.apply_symm_apply]
  let x₁ : X _⦋0⦌ := X.δ 0 raw
  let e : SSet.Edge x₀ x₁ := SSet.Edge.mk raw hsrc rfl
  have he : e.IsEquivalence :=
    (SSet.joyalInterval.isEquivalence_forward l).of_edge_eq rfl
  have hmap : (e.map p).edge = g.edge := by
    change p.app (op ⦋1⦌) (SSet.yonedaEquiv (SSet.joyalInterval.forward ≫ l)) = g.edge
    rw [← SSet.yonedaEquiv_comp, Category.assoc]
    change SSet.yonedaEquiv (SSet.joyalInterval.forward ≫ (sq.lift ≫ p)) = g.edge
    rw [sq.fac_right, ht, Equiv.apply_symm_apply]
  have htarget : p.app (op ⦋0⦌) x₁ = y₁ := by
    calc p.app (op ⦋0⦌) x₁ = Y.δ 0 (e.map p).edge := (e.map p).tgt_eq.symm
      _ = Y.δ 0 g.edge := by rw [hmap]
      _ = y₁ := g.tgt_eq
  exact ⟨x₁, htarget, e, he, hmap⟩

private lemma genuine_of_inner_strict {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] [SSet.InnerFibration p]
    [SSet.HasStrictEquivalenceLifting p] : SSet.categoricalFibrations p := by
  let : SSet.Quasicategory X := SSet.quasicategory_of_innerFibration p
  rw [SSet.categoricalFibrations.mem_iff]
  intro A B i hi hweak
  let : Mono i := hi
  let sq := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  let : SSet.HasStrictEquivalenceLifting sq.π :=
    SSet.hasStrictEquivalenceLifting_pullbackObjObjπ sq
  exact square_lifting_of_strict_packet i hweak sq

/-- A map to a quasicategory is a genuine categorical fibration exactly when it is
inner and lifts the original equivalence edges strictly. -/
public theorem categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] :
    SSet.categoricalFibrations p ↔
      SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p := by
  constructor
  · exact inner_strict_of_genuine p
  · rintro ⟨hinner, hstrict⟩
    let : SSet.InnerFibration p := hinner
    let : SSet.HasStrictEquivalenceLifting p := hstrict
    exact genuine_of_inner_strict p

/-- A map to a quasicategory is a genuine categorical fibration exactly when it is
inner and its original ordinary homotopy-category functor is an isofibration. -/
public theorem categoricalFibrations_iff_innerFibration_and_hoIsofibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] :
    SSet.categoricalFibrations p ↔
      SSet.InnerFibration p ∧ (SSet.hoFunctor.map p).toFunctor.IsIsofibration := by
  rw [categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting]
  constructor
  · rintro ⟨hinner, hstrict⟩
    let : SSet.InnerFibration p := hinner
    exact ⟨hinner, (SSet.isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting p).mpr hstrict⟩
  · rintro ⟨hinner, hiso⟩
    let : SSet.InnerFibration p := hinner
    exact ⟨hinner, (SSet.isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting p).mp hiso⟩

/-- The full actual coherent endpoint criterion at a quasicategory codomain. -/
public theorem categoricalFibrations_iff_innerFibration_and_coherentIsoEndpointLifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.Quasicategory Y] :
    SSet.categoricalFibrations p ↔ SSet.InnerFibration p ∧
      HasLiftingProperty SSet.coherentIso.endpointInclusion p := by
  rw [categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting]
  constructor
  · rintro ⟨hinner, hstrict⟩
    let : SSet.InnerFibration p := hinner
    exact ⟨hinner, (hasStrictEquivalenceLifting_iff_hasLiftingProperty_coherentIso_endpointInclusion p).mp hstrict⟩
  · rintro ⟨hinner, hcoherent⟩
    let : SSet.InnerFibration p := hinner
    exact ⟨hinner, (hasStrictEquivalenceLifting_iff_hasLiftingProperty_coherentIso_endpointInclusion p).mpr hcoherent⟩

/-- The actual finite-interval naive criterion follows from the genuine class
bridge and the strict fibration criterion. -/
public theorem joyalInterval.auxiliaryNaiveFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.Quasicategory Y] :
    SSet.joyalInterval.auxiliaryNaiveFibrations p ↔
      SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p :=
  (joyalInterval.categoricalFibrations_iff_auxiliaryNaiveFibrations p).symm.trans (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p)

end SSet
