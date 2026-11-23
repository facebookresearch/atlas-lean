/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.MetricDomination
import MathlibExt.Topology.Category.TopCat.RealizedBasedWhitehead
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularHomotopyRelAtPoint
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyRelAtVertex
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# The original singular counit and CW type from actual domination

The constructed counit inverse retains its exact point and both complete
relative inverse families. Open normed spaces and their actual continuous
retracts use the neutral metric CW domination construction.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology Set Function
open scoped Simplicial TopCat.modelCategory SSet.modelCategoryQuillen unitInterval

universe u

namespace Topology.CWComplex.SingularCWType

private abbrev singularRealization : TopCat.{u} ⥤ TopCat.{u} :=
  TopCat.toSSet ⋙ SSet.toTop

private abbrev C (X : TopCat.{u}) : TopCat.{u} := singularRealization.obj X

private def epsilon (X : TopCat.{u}) : C X ⟶ X := sSetTopAdj.counit.app X

private def singularVertex (X : TopCat.{u}) (x : X) :
    (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x

private def cPoint (X : TopCat.{u}) (x : X) : C X :=
  SSet.realizedVertex (singularVertex X x)

private theorem epsilon_point (X : TopCat.{u}) (x : X) :
    epsilon X (cPoint X x) = x :=
  (TopCat.counit_realizedVertex (singularVertex X x)).trans
    (TopCat.toSSetObj₀Equiv.apply_symm_apply x)

private theorem epsilon_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    singularRealization.map f ≫ epsilon Y = epsilon X ≫ f :=
  sSetTopAdj.counit.naturality f

private theorem singularVertex_map {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (singularVertex X x) =
      singularVertex Y (f x) := by
  apply TopCat.toSSetObj₀Equiv.injective
  dsimp only [singularVertex]
  rw [TopCat.toSSetObj₀Equiv.apply_symm_apply]
  rfl

private theorem cPoint_map {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    singularRealization.map f (cPoint X x) = cPoint Y (f x) := by
  change SSet.toTop.map (TopCat.toSSet.map f) (SSet.realizedVertex (singularVertex X x)) = _
  rw [← SSet.realizedVertex_naturality, singularVertex_map]
  rfl

/-- Precomposition of the actual relative homotopy, with its point law explicit. -/
private def precompRelative {X Y Z : TopCat.{u}} {f g : X ⟶ Y} (x : X)
    (H : ContinuousMap.HomotopyRel f.hom g.hom {x}) (p : Z ⟶ X)
    (z : Z) (hp : p z = x) :
    ContinuousMap.HomotopyRel (p ≫ f).hom (p ≫ g).hom {z} where
  toHomotopy := (H.toHomotopy.compContinuousMap p.hom).cast
    (TopCat.hom_comp p f).symm (TopCat.hom_comp p g).symm
  prop' t z' hz' := by
    have hz : z' = z := Set.mem_singleton_iff.mp hz'
    subst z'
    change H (t, p z) = f (p z)
    rw [hp]
    exact H.eq_fst t (Set.mem_singleton x)

private def whiskerRelative {X Y Z T : TopCat.{u}} {f g : X ⟶ Y} (x : X)
    (H : ContinuousMap.HomotopyRel f.hom g.hom {x}) (p : Z ⟶ X) (q : Y ⟶ T)
    (z : Z) (hp : p z = x) :
    ContinuousMap.HomotopyRel (p ≫ f ≫ q).hom (p ≫ g ≫ q).hom {z} := by
  let F := (precompRelative x H p z hp).compContinuousMap q.hom
  exact F.cast (by simp only [TopCat.hom_comp]; rfl)
    (by simp only [TopCat.hom_comp]; rfl)

/-- Singularize the actual stationary homotopy and realize its literal point. -/
private def realizedSingularRelative {X Y : TopCat.{u}} {f g : X ⟶ Y} (x : X)
    (H : ContinuousMap.HomotopyRel f.hom g.hom {x}) :
    ContinuousMap.HomotopyRel (singularRealization.map f).hom
      (singularRealization.map g).hom {cPoint X x} := by
  let HS := TopCat.singularHomotopyRelAtPoint x H
  have hx : singularVertex X x ∈
      (SSet.Subcomplex.range (SSet.const (X := (Δ[0] : SSet.{u}))
        (singularVertex X x))).obj (Opposite.op ⦋0⦌) := by
    change singularVertex X x ∈ Set.range
      ((SSet.const (X := (Δ[0] : SSet.{u}))
        (singularVertex X x)).app (Opposite.op ⦋0⦌))
    refine ⟨SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌), ?_⟩
    rw [← SSet.yonedaEquiv_symm_zero,
      SSet.yonedaEquiv_symm_app_objEquiv_symm]
    simp
  exact SSet.realizeHomotopyRelAtVertex HS (singularVertex X x) hx


/-- Private constructed data for the original counit, including both actual relative families. -/
private structure CounitInverseData (X : TopCat.{u}) (x : X) where
  inv : X ⟶ C X
  inv_point : inv x = cPoint X x
  left : ContinuousMap.HomotopyRel (epsilon X ≫ inv).hom (TopCat.Hom.hom (𝟙 (C X))) {cPoint X x}
  right : ContinuousMap.HomotopyRel (inv ≫ epsilon X).hom (TopCat.Hom.hom (𝟙 X)) {x}

/-- The actual realization counit has its based inverse from the proved realized Whitehead API. -/
private def realizedCounitInverse (K : SSet.{u}) (v : K _⦋0⦌) :
    CounitInverseData (SSet.toTop.obj K) (SSet.realizedVertex v) := by
  let X : TopCat.{u} := SSet.toTop.obj K
  let x : X := SSet.realizedVertex v
  let sv : (TopCat.toSSet.obj X) _⦋0⦌ := singularVertex X x
  let f : C X ⟶ X := epsilon X
  have hf : TopCat.weakHomotopyEquivalences f :=
    SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X
  have hpoint : f (SSet.realizedVertex sv) = SSet.realizedVertex v := epsilon_point X x
  exact
    { inv := TopCat.realizedBasedHomotopyInverse sv v f hpoint hf
      inv_point := TopCat.realizedBasedHomotopyInverse_point sv v f hpoint hf
      left := TopCat.realizedBasedLeftHomotopy sv v f hpoint hf
      right := TopCat.realizedBasedRightHomotopy sv v f hpoint hf }

/-- Transport the constructed inverse to the ORIGINAL counit along an actual pointed iso. -/
private def transportCounitInverse {X Y : TopCat.{u}} (i : X ≅ Y) (x : X) (y : Y)
    (hpoint : i.hom x = y) (D : CounitInverseData X x) : CounitInverseData Y y := by
  have hInv : i.inv y = x := by
    calc
      i.inv y = i.inv (i.hom x) := congrArg i.inv hpoint.symm
      _ = x := by
        simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
          ConcreteCategory.congr_hom i.hom_inv_id x
  let r : Y ⟶ C Y := i.inv ≫ D.inv ≫ singularRealization.map i.hom
  have hrpoint : r y = cPoint Y y := by
    change singularRealization.map i.hom (D.inv (i.inv y)) = _
    rw [hInv, D.inv_point, cPoint_map, hpoint]
  let HL := whiskerRelative (cPoint X x) D.left
    (singularRealization.map i.inv) (singularRealization.map i.hom) (cPoint Y y)
    (by rw [cPoint_map, hInv])
  have hLS : singularRealization.map i.inv ≫ (epsilon X ≫ D.inv) ≫
      singularRealization.map i.hom = epsilon Y ≫ r := by
    calc
      _ = (singularRealization.map i.inv ≫ epsilon X) ≫ D.inv ≫
          singularRealization.map i.hom := by simp only [Category.assoc]
      _ = (epsilon Y ≫ i.inv) ≫ D.inv ≫ singularRealization.map i.hom := by
        rw [epsilon_naturality i.inv]
      _ = epsilon Y ≫ r := by simp only [r, Category.assoc]
  have hLT : singularRealization.map i.inv ≫ (𝟙 (C X)) ≫
      singularRealization.map i.hom = 𝟙 (C Y) := by
    calc
      _ = singularRealization.map i.inv ≫ singularRealization.map i.hom := by simp
      _ = singularRealization.map (i.inv ≫ i.hom) :=
        (singularRealization.map_comp i.inv i.hom).symm
      _ = 𝟙 (C Y) := by rw [i.inv_hom_id, CategoryTheory.Functor.map_id]
  let HR := whiskerRelative x D.right i.inv i.hom y hInv
  have hRS : i.inv ≫ (D.inv ≫ epsilon X) ≫ i.hom = r ≫ epsilon Y := by
    dsimp only [r]
    simp only [Category.assoc]
    rw [← epsilon_naturality i.hom]
  have hRT : i.inv ≫ (𝟙 X) ≫ i.hom = 𝟙 Y := by simp
  exact
    { inv := r
      inv_point := hrpoint
      left := HL.cast
        (congrArg (fun f : C Y ⟶ C Y => f.hom) hLS)
        (congrArg (fun f : C Y ⟶ C Y => f.hom) hLT)
      right := HR.cast
        (congrArg (fun f : Y ⟶ Y => f.hom) hRS)
        (congrArg (fun f : Y ⟶ Y => f.hom) hRT) }

/-- The weak nerve's actual counit inverse comes from its canonical realized face-nerve model. -/
private def nerveCounitInverse {J : Type u} (Q : PreAbstractSimplicialComplex J)
    (v0 : J) (hv0 : {v0} ∈ Q) :
    CounitInverseData (TopCat.of Q.Realization)
      (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) := by
  let K : SSet.{u} := PreAbstractSimplicialComplex.faceNerve Q
  let x : K _⦋0⦌ := PreAbstractSimplicialComplex.faceNerveVertex Q v0 hv0
  let i : SSet.toTop.obj K ≅ TopCat.of Q.Realization :=
    TopCat.isoOfHomeo (PreAbstractSimplicialComplex.Realization.affineHomeomorph Q)
  have hpoint : i.hom (SSet.realizedVertex x) =
      PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0 := by
    change PreAbstractSimplicialComplex.Realization.affineHomeomorph Q
      (SSet.realizedVertex (PreAbstractSimplicialComplex.faceNerveVertex Q v0 hv0)) = _
    exact PreAbstractSimplicialComplex.Realization.affineHomeomorph_vertex Q v0 hv0
  exact transportCounitInverse i (SSet.realizedVertex x)
    (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) hpoint
    (realizedCounitInverse K x)

/-- The actual R is the stated composite; both inverse homotopies are constructed. -/
private def inverseFromDomination {M N : TopCat.{u}} (e : M) (n0 : N)
    (p : M ⟶ N) (q : N ⟶ M) (hp : p e = n0) (hq : q n0 = e)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom (TopCat.Hom.hom (𝟙 M)) {e})
    (DN : CounitInverseData N n0) : CounitInverseData M e := by
  let R : M ⟶ C M := p ≫ DN.inv ≫ singularRealization.map q
  have hRpoint : R e = cPoint M e := by
    change singularRealization.map q (DN.inv (p e)) = _
    rw [hp, DN.inv_point, cPoint_map, hq]
  let HR := whiskerRelative n0 DN.right p q e hp
  have hRS : p ≫ (DN.inv ≫ epsilon N) ≫ q = R ≫ epsilon M := by
    dsimp only [R]
    simp only [Category.assoc]
    rw [← epsilon_naturality q]
  have hRT : p ≫ (𝟙 N) ≫ q = p ≫ q := by simp
  let HR' : ContinuousMap.HomotopyRel (R ≫ epsilon M).hom (p ≫ q).hom {e} :=
    HR.cast (congrArg (fun f : M ⟶ M => f.hom) hRS)
      (congrArg (fun f : M ⟶ M => f.hom) hRT)
  let HL := whiskerRelative (cPoint N n0) DN.left
    (singularRealization.map p) (singularRealization.map q) (cPoint M e)
    (by rw [cPoint_map, hp])
  have hLS : singularRealization.map p ≫ (epsilon N ≫ DN.inv) ≫
      singularRealization.map q = epsilon M ≫ R := by
    calc
      _ = (singularRealization.map p ≫ epsilon N) ≫ DN.inv ≫
          singularRealization.map q := by simp only [Category.assoc]
      _ = (epsilon M ≫ p) ≫ DN.inv ≫ singularRealization.map q := by
        rw [epsilon_naturality p]
      _ = epsilon M ≫ R := by simp only [R, Category.assoc]
  have hLT : singularRealization.map p ≫ (𝟙 (C N)) ≫
      singularRealization.map q = singularRealization.map (p ≫ q) := by
    simp only [Category.id_comp]
    exact (singularRealization.map_comp p q).symm
  let HL' : ContinuousMap.HomotopyRel (epsilon M ≫ R).hom
      (singularRealization.map (p ≫ q)).hom {cPoint M e} :=
    HL.cast (congrArg (fun f : C M ⟶ C M => f.hom) hLS)
      (congrArg (fun f : C M ⟶ C M => f.hom) hLT)
  let HG : ContinuousMap.HomotopyRel (singularRealization.map (p ≫ q)).hom
      (TopCat.Hom.hom (𝟙 (C M))) {cPoint M e} :=
    (realizedSingularRelative e Hdom).cast rfl
      (congrArg (fun f : C M ⟶ C M => f.hom) (singularRealization.map_id M))
  exact
    { inv := R
      inv_point := hRpoint
      left := HL'.trans HG
      right := HR'.trans Hdom }

/-- The returned inverse is literally |Sing q| ∘ k ∘ p; no chosen second inverse is inserted. -/
private theorem inverseFromDomination_inv {M N : TopCat.{u}} (e : M) (n0 : N)
    (p : M ⟶ N) (q : N ⟶ M) (hp : p e = n0) (hq : q n0 = e)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom (TopCat.Hom.hom (𝟙 M)) {e})
    (DN : CounitInverseData N n0) :
    (inverseFromDomination e n0 p q hp hq Hdom DN).inv =
      p ≫ DN.inv ≫ SSet.toTop.map (TopCat.toSSet.map q) := (rfl)

private theorem inverse_left_fixed {X : TopCat.{u}} {x : X} (D : CounitInverseData X x)
    (t : unitInterval) : D.left (t, cPoint X x) = cPoint X x :=
  D.left.eq_snd t (Set.mem_singleton _)

private theorem inverse_right_fixed {X : TopCat.{u}} {x : X} (D : CounitInverseData X x)
    (t : unitInterval) : D.right (t, x) = x :=
  D.right.eq_snd t (Set.mem_singleton _)

private def inverseHomotopyEquiv {X : TopCat.{u}} {x : X} (D : CounitInverseData X x) :
    ContinuousMap.HomotopyEquiv (C X) X where
  toFun := (epsilon X).hom
  invFun := D.inv.hom
  left_inv := ⟨D.left.toHomotopy.cast (TopCat.hom_comp _ _) TopCat.hom_id⟩
  right_inv := ⟨D.right.toHomotopy.cast (TopCat.hom_comp _ _) TopCat.hom_id⟩

private theorem inverseHomotopyEquiv_toFun {X : TopCat.{u}} {x : X} (D : CounitInverseData X x) :
    (inverseHomotopyEquiv D).toFun = (sSetTopAdj.counit.app X).hom := (rfl)

private theorem inverseHomotopyEquiv_invFun {X : TopCat.{u}} {x : X} (D : CounitInverseData X x) :
    (inverseHomotopyEquiv D).invFun = D.inv.hom := (rfl)

/-- Instantiate the generic recipe with the DERIVED counit inverse of the actual weak nerve. -/
private def nerveDominationInverse {J : Type u} (Q : PreAbstractSimplicialComplex J)
    (v0 : J) (hv0 : {v0} ∈ Q) (M : TopCat.{u}) (e : M)
    (p : M ⟶ TopCat.of Q.Realization) (q : TopCat.of Q.Realization ⟶ M)
    (hp : p e = PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0)
    (hq : q (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) = e)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom (TopCat.Hom.hom (𝟙 M)) {e}) :
    CounitInverseData M e :=
  inverseFromDomination e
    (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) p q hp hq Hdom
    (nerveCounitInverse Q v0 hv0)

/-- Complete original-counit point model from the actual weak-nerve domination data. -/
private theorem singularCWModel_of_domination {J : Type u}
    (Q : PreAbstractSimplicialComplex J) (v0 : J) (hv0 : {v0} ∈ Q)
    (M : TopCat.{u}) (e : M)
    (p : M ⟶ TopCat.of Q.Realization) (q : TopCat.of Q.Realization ⟶ M)
    (hp : p e = PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0)
    (hq : q (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) = e)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom (TopCat.Hom.hom (𝟙 M)) {e}) :
    let S : SSet.{u} := TopCat.toSSet.obj M
    let C₀ : TopCat.{u} := SSet.toTop.obj S
    let c₀ : C₀ := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
    let cw := SSet.realizationClassicalCWComplex S
    letI : Topology.CWComplex (Set.univ : Set C₀) := cw
    T2Space C₀ ∧
      (∃ j : Topology.CWComplex.cell (Set.univ : Set C₀) 0,
        ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = c₀) ∧
      ∃ R : M ⟶ C₀,
        R = p ≫ (nerveCounitInverse Q v0 hv0).inv ≫ SSet.toTop.map (TopCat.toSSet.map q) ∧
        R e = c₀ ∧ sSetTopAdj.counit.app M c₀ = e ∧
        ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app M ≫ R).hom
            (TopCat.Hom.hom (𝟙 C₀)) {c₀},
          ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app M).hom
              (TopCat.Hom.hom (𝟙 M)) {e},
            (∀ t : unitInterval, HL (t, c₀) = c₀) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ E : ContinuousMap.HomotopyEquiv C₀ M,
              E.toFun = (sSetTopAdj.counit.app M).hom ∧ E.invFun = R.hom := by
  let D := nerveDominationInverse Q v0 hv0 M e p q hp hq Hdom
  refine ⟨SSet.realization_t2Space (TopCat.toSSet.obj M),
    SSet.realizedVertex_is_classical_zeroCell (TopCat.toSSetObj₀Equiv.symm e),
    D.inv, ?_, D.inv_point, epsilon_point M e, D.left, D.right,
    inverse_left_fixed D, inverse_right_fixed D, inverseHomotopyEquiv D,
    inverseHomotopyEquiv_toFun D, inverseHomotopyEquiv_invFun D⟩
  exact inverseFromDomination_inv e
    (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) p q hp hq Hdom
    (nerveCounitInverse Q v0 hv0)

/-- The original singular counit point model obtained from actual pointed CW domination data.
The inverse and both complete relative families are the existing constructed witnesses. -/
public theorem singularCWPointModelOfDomination {J : Type u}
    (Q : PreAbstractSimplicialComplex J) (v0 : J) (hv0 : {v0} ∈ Q)
    (M : TopCat.{u}) (e : M)
    (p : M ⟶ TopCat.of Q.Realization) (q : TopCat.of Q.Realization ⟶ M)
    (hp : p e = PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0)
    (hq : q (PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0) = e)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom (TopCat.Hom.hom (𝟙 M)) {e}) :
    let S : SSet.{u} := TopCat.toSSet.obj M
    let C₀ : TopCat.{u} := SSet.toTop.obj S
    let c₀ : C₀ := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
    let cw := SSet.realizationClassicalCWComplex S
    letI : Topology.CWComplex (Set.univ : Set C₀) := cw
    T2Space C₀ ∧
      (∃ j : Topology.CWComplex.cell (Set.univ : Set C₀) 0,
        ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = c₀) ∧
      ∃ R : M ⟶ C₀,
        R e = c₀ ∧ sSetTopAdj.counit.app M c₀ = e ∧
        ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app M ≫ R).hom
            (TopCat.Hom.hom (𝟙 C₀)) {c₀},
          ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app M).hom
              (TopCat.Hom.hom (𝟙 M)) {e},
            (∀ t : unitInterval, HL (t, c₀) = c₀) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ E : ContinuousMap.HomotopyEquiv C₀ M,
              E.toFun = (sSetTopAdj.counit.app M).hom ∧ E.invFun = R.hom := by
  obtain ⟨hC, hzero, R, _, hRpoint, hepsilon, HL, HR, hLfixed, hRfixed, E, hEto, hEinv⟩ :=
    singularCWModel_of_domination Q v0 hv0 M e p q hp hq Hdom
  exact ⟨hC, hzero, R, hRpoint, hepsilon, HL, HR, hLfixed, hRfixed, E, hEto, hEinv⟩

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem openNormedCounitInverse_nonempty (U : Set E) (hU : IsOpen U) (e : U) :
    Nonempty (CounitInverseData (TopCat.of U) e) := by
  obtain ⟨J, Q, W, v0, hv0, _, _, _, _, _, hdata⟩ :=
    Topology.openNormedCWDomination U hU e
  obtain ⟨p, q, hp, hq, Hdom, _, _⟩ := hdata
  let p' : TopCat.of U ⟶ TopCat.of Q.Realization := TopCat.ofHom p
  let q' : TopCat.of Q.Realization ⟶ TopCat.of U := TopCat.ofHom q
  let Hdom' : ContinuousMap.HomotopyRel (p' ≫ q').hom
      (TopCat.Hom.hom (𝟙 (TopCat.of U))) {e} :=
    Hdom.cast (by simp only [p', q', TopCat.hom_comp, TopCat.hom_ofHom])
      (TopCat.hom_id (X := TopCat.of U)).symm
  exact ⟨nerveDominationInverse Q v0 hv0 (TopCat.of U) e p' q' hp hq Hdom'⟩

private def openNormedCounitInverse (U : Set E) (hU : IsOpen U) (e : U) :
    CounitInverseData (TopCat.of U) e :=
  Classical.choice (openNormedCounitInverse_nonempty U hU e)

private def openNormedRetractCounitInverse {M : Type u} [TopologicalSpace M]
    (U : Set E) (hU : IsOpen U) (i : C(M, U)) (r : C(U, M))
    (hri : r.comp i = ContinuousMap.id M) (m : M) :
    CounitInverseData (TopCat.of M) m := by
  let p : TopCat.of M ⟶ TopCat.of U := TopCat.ofHom i
  let q : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom r
  have hcomp : (p ≫ q).hom = ContinuousMap.id M := by
    change r.comp i = ContinuousMap.id M
    exact hri
  let Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom
      (TopCat.Hom.hom (𝟙 (TopCat.of M))) {m} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id M) {m}).cast hcomp.symm
      (TopCat.hom_id (X := TopCat.of M)).symm
  have hq : q (i m) = m := DFunLike.congr_fun hri m
  exact inverseFromDomination m (i m) p q rfl hq Hdom
    (openNormedCounitInverse U hU (i m))

private theorem counitInverseDataCWType (X : TopCat.{u}) (m : X)
    (D : CounitInverseData X m) :
    let Z : TopCat.{u} := SSet.toTop.obj (TopCat.toSSet.obj X)
    let z0 : Z := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm m)
    T2Space Z ∧
      (∃ cw : Topology.CWComplex (Set.univ : Set Z),
        ∃ j : cw.cell 0, ∀ x : Fin 0 → ℝ, cw.map 0 j x = z0) ∧
      ∃ R : X ⟶ Z, R m = z0 ∧ sSetTopAdj.counit.app X z0 = m ∧
        ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ R).hom
            (TopCat.Hom.hom (𝟙 Z)) {z0},
          ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app X).hom
              (TopCat.Hom.hom (𝟙 X)) {m},
            (∀ t : unitInterval, HL (t, z0) = z0) ∧
            (∀ t : unitInterval, HR (t, m) = m) ∧
            ∃ A : ContinuousMap.HomotopyEquiv Z X,
              A.toFun = (sSetTopAdj.counit.app X).hom ∧ A.invFun = R.hom := by
  let Z : TopCat.{u} := SSet.toTop.obj (TopCat.toSSet.obj X)
  let z0 : Z := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm m)
  let cw : Topology.CWComplex (Set.univ : Set Z) :=
    SSet.realizationClassicalCWComplex (TopCat.toSSet.obj X)
  have hZero : ∃ j : cw.cell 0, ∀ x : Fin 0 → ℝ, cw.map 0 j x = z0 :=
    SSet.realizedVertex_is_classical_zeroCell (TopCat.toSSetObj₀Equiv.symm m)
  have hCW : ∃ c : Topology.CWComplex (Set.univ : Set Z),
      ∃ j : c.cell 0, ∀ x : Fin 0 → ℝ, c.map 0 j x = z0 := ⟨cw, hZero⟩
  have hT2 : T2Space Z := SSet.realization_t2Space (TopCat.toSSet.obj X)
  let R : X ⟶ Z := D.inv
  have hPoint : R m = z0 := D.inv_point
  have hCounitPoint : sSetTopAdj.counit.app X z0 = m := epsilon_point X m
  let HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ R).hom
      (TopCat.Hom.hom (𝟙 Z)) {z0} := D.left
  let HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app X).hom
      (TopCat.Hom.hom (𝟙 X)) {m} := D.right
  have hLeft : ∀ t : unitInterval, HL (t, z0) = z0 := inverse_left_fixed D
  have hRight : ∀ t : unitInterval, HR (t, m) = m := inverse_right_fixed D
  let A : ContinuousMap.HomotopyEquiv Z X := inverseHomotopyEquiv D
  have hForward : A.toFun = (sSetTopAdj.counit.app X).hom := inverseHomotopyEquiv_toFun D
  have hInverse : A.invFun = R.hom := inverseHomotopyEquiv_invFun D
  exact ⟨hT2, hCW, R, hPoint, hCounitPoint, HL, HR, hLeft, hRight, A, hForward, hInverse⟩

end Topology.CWComplex.SingularCWType

public section

namespace TopCat

open Topology.CWComplex.SingularCWType

/-- A genuine continuous retract of an open normed space has CW type.
The inverse is constructed for its actual singular counit, with both complete
point-relative inverse families. No CW or counit-inverse outcome is supplied. -/
theorem cwType_of_openNormedRetract {E M : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (U : Set E) (hU : IsOpen U) (i : C(M, U)) (r : C(U, M))
    (hri : r.comp i = ContinuousMap.id M) (m : M) :
    let X : TopCat.{u} := TopCat.of M
    let Z : TopCat.{u} := SSet.toTop.obj (TopCat.toSSet.obj X)
    let z0 : Z := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm m)
    T2Space Z ∧
      (∃ cw : Topology.CWComplex (Set.univ : Set Z),
        ∃ j : cw.cell 0, ∀ x : Fin 0 → ℝ, cw.map 0 j x = z0) ∧
      ∃ R : X ⟶ Z, R m = z0 ∧ sSetTopAdj.counit.app X z0 = m ∧
        ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ R).hom
            (TopCat.Hom.hom (𝟙 Z)) {z0},
          ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app X).hom
              (TopCat.Hom.hom (𝟙 X)) {m},
            (∀ t : unitInterval, HL (t, z0) = z0) ∧
            (∀ t : unitInterval, HR (t, m) = m) ∧
            ∃ A : ContinuousMap.HomotopyEquiv Z X,
              A.toFun = (sSetTopAdj.counit.app X).hom ∧ A.invFun = R.hom := by
  let X : TopCat.{u} := TopCat.of M
  let D : CounitInverseData X m := openNormedRetractCounitInverse U hU i r hri m
  exact counitInverseDataCWType X m D

/-- The actual singular counit of an open normed space has a based inverse and
both whole inverse homotopies, derived through its constructed CW domination. -/
theorem cwType_of_openNormedSpace {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (e : U) :
    let X : TopCat.{u} := TopCat.of U
    let Z : TopCat.{u} := SSet.toTop.obj (TopCat.toSSet.obj X)
    let z0 : Z := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
    T2Space Z ∧
      (∃ cw : Topology.CWComplex (Set.univ : Set Z),
        ∃ j : cw.cell 0, ∀ x : Fin 0 → ℝ, cw.map 0 j x = z0) ∧
      ∃ R : X ⟶ Z, R e = z0 ∧ sSetTopAdj.counit.app X z0 = e ∧
        ∃ HL : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ R).hom
            (TopCat.Hom.hom (𝟙 Z)) {z0},
          ∃ HR : ContinuousMap.HomotopyRel (R ≫ sSetTopAdj.counit.app X).hom
              (TopCat.Hom.hom (𝟙 X)) {e},
            (∀ t : unitInterval, HL (t, z0) = z0) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ A : ContinuousMap.HomotopyEquiv Z X,
              A.toFun = (sSetTopAdj.counit.app X).hom ∧ A.invFun = R.hom := by
  exact cwType_of_openNormedRetract U hU (ContinuousMap.id U) (ContinuousMap.id U) rfl e

end TopCat


public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe uCounit

namespace TopCat

/-- An inverse of the original singular counit, with its point equation and
both complete inverse homotopies relative to the specified point. -/
structure SingularCounitPointInverseData (X : TopCat.{uCounit}) (x : X) where
  /-- The actual inverse of the literal original realization--singular counit. -/
  inverse : X ⟶ SSet.toTop.obj (TopCat.toSSet.obj X)
  inverse_point : inverse x = SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  /-- The complete realization-side inverse family fixes the literal singular vertex. -/
  left : ContinuousMap.HomotopyRel (sSetTopAdj.counit.app X ≫ inverse).hom
    ((𝟙 (SSet.toTop.obj (TopCat.toSSet.obj X)) :
      SSet.toTop.obj (TopCat.toSSet.obj X) ⟶ SSet.toTop.obj (TopCat.toSSet.obj X)).hom)
    {SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)}
  /-- The complete original-space inverse family fixes the entire specified point. -/
  right : ContinuousMap.HomotopyRel (inverse ≫ sSetTopAdj.counit.app X).hom
    ((𝟙 X : X ⟶ X).hom) {x}

namespace SingularCounitPointInverseData

variable {X : TopCat.{uCounit}} {x : X} (D : SingularCounitPointInverseData X x)

/-- The literal original counit and its supplied inverse form the space equivalence. -/
def equiv : ContinuousMap.HomotopyEquiv (SSet.toTop.obj (TopCat.toSSet.obj X)) X where
  toFun := (sSetTopAdj.counit.app X).hom
  invFun := D.inverse.hom
  left_inv := ⟨D.left.toHomotopy.cast
    (TopCat.hom_comp (sSetTopAdj.counit.app X) D.inverse)
    (TopCat.hom_id (X := SSet.toTop.obj (TopCat.toSSet.obj X)))⟩
  right_inv := ⟨D.right.toHomotopy.cast
    (TopCat.hom_comp D.inverse (sSetTopAdj.counit.app X)) (TopCat.hom_id (X := X))⟩

private theorem equivForwardComputed : D.equiv.toFun = (sSetTopAdj.counit.app X).hom := rfl

/-- The entire forward is the same original singular counit. -/
theorem equiv_toFun : D.equiv.toFun = (sSetTopAdj.counit.app X).hom := equivForwardComputed D

private theorem equivInverseComputed : D.equiv.invFun = D.inverse.hom := rfl

/-- The whole return map is exactly the same stored counit inverse. -/
theorem equiv_invFun : D.equiv.invFun = D.inverse.hom := equivInverseComputed D

/-- Every realization-side inverse time fixes the literal singular vertex. -/
theorem left_fixed (t : unitInterval) :
    D.left (t, SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)) =
      SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x) :=
  D.left.eq_snd t (Set.mem_singleton _)

/-- Every original-space inverse time fixes its entire specified point. -/
theorem right_fixed (t : unitInterval) : D.right (t, x) = x :=
  D.right.eq_snd t (Set.mem_singleton _)

end SingularCounitPointInverseData

end TopCat

namespace Topology.CWComplex.SingularCWType

private def publicCounitInverseTransfer {M N : TopCat.{uCounit}} (m : M) (n : N)
    (p : M ⟶ N) (q : N ⟶ M) (hp : p m = n) (hq : q n = m)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom ((𝟙 M : M ⟶ M).hom) {m})
    (D : TopCat.SingularCounitPointInverseData N n) :
    TopCat.SingularCounitPointInverseData M m := by
  let DN : CounitInverseData N n :=
    { inv := D.inverse
      inv_point := D.inverse_point
      left := D.left
      right := D.right }
  let DM := inverseFromDomination m n p q hp hq Hdom DN
  exact
    { inverse := DM.inv
      inverse_point := DM.inv_point
      left := DM.left
      right := DM.right }

end Topology.CWComplex.SingularCWType

namespace TopCat

/-- Pointed domination transfers the original singular-counit inverse,
using the same canonical construction and both complete relative families. -/
@[no_expose]
def singularCounitInverseOfPointedDomination {M N : TopCat.{uCounit}} (m : M) (n : N)
    (p : M ⟶ N) (q : N ⟶ M) (hp : p m = n) (hq : q n = m)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom ((𝟙 M : M ⟶ M).hom) {m})
    (D : SingularCounitPointInverseData N n) : SingularCounitPointInverseData M m :=
  Topology.CWComplex.SingularCWType.publicCounitInverseTransfer m n p q hp hq Hdom D

private theorem singularCounitInverseTransferProgram {M N : TopCat.{uCounit}}
    (m : M) (n : N) (p : M ⟶ N) (q : N ⟶ M) (hp : p m = n) (hq : q n = m)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom ((𝟙 M : M ⟶ M).hom) {m})
    (D : SingularCounitPointInverseData N n) :
    (singularCounitInverseOfPointedDomination m n p q hp hq Hdom D).inverse =
      p ≫ D.inverse ≫ SSet.toTop.map (TopCat.toSSet.map q) := rfl

/-- The transferred inverse keeps the literal original three-map program. -/
theorem singularCounitInverseOfPointedDomination_inverse {M N : TopCat.{uCounit}}
    (m : M) (n : N) (p : M ⟶ N) (q : N ⟶ M) (hp : p m = n) (hq : q n = m)
    (Hdom : ContinuousMap.HomotopyRel (p ≫ q).hom ((𝟙 M : M ⟶ M).hom) {m})
    (D : SingularCounitPointInverseData N n) :
    (singularCounitInverseOfPointedDomination m n p q hp hq Hdom D).inverse =
      p ≫ D.inverse ≫ SSet.toTop.map (TopCat.toSSet.map q) :=
  singularCounitInverseTransferProgram m n p q hp hq Hdom D

end TopCat

end
