/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeNerveUnitComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangePathFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MappingPathFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyFiberRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Actual native covers and the fiber of the original nerve unit

The original unit induces an equivalence on fundamental groupoids. The
computed Cartesian native-cover comparison is consequently an isomorphism.
The actual cover of the groupoid-nerve base is contractible. The existing
native-cover path-fiber map then gives a span of weak maps from the same
ending-path carrier to the literal native cover and to the unit fiber.
Both maps have the same original projection to X.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet

private theorem pointFiberProjection_mem_realizationWeakEquivalences
    (X : SSet.{u}) [KanComplex X] (b : (Δ[0] : SSet.{u}) _⦋0⦌) :
    realizationWeakEquivalences (pathHomotopyFiberToTotal
      (stdSimplex.isTerminalObj₀.from X) b) := by
  let f : X ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from X
  let k : (Δ[0] : SSet.{u}) ⟶ Δ[0] := SSet.const b
  have hk : k = 𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  let : IsIso k := hk.symm ▸ (inferInstance : IsIso (𝟙 (Δ[0] : SSet.{u})))
  let : Fibration f :=
    (isFibrant_iff_of_isTerminal f stdSimplex.isTerminalObj₀).mp (inferInstance : IsFibrant X)
  have hFiber : IsIso (Subcomplex.fiber f b).ι :=
    (Subcomplex.fiber_isPullback f b).isIso_fst_of_isIso
  let : IsIso (Subcomplex.fiber f b).ι := hFiber
  have hIncl : realizationWeakEquivalences (Subcomplex.fiber f b).ι :=
    (weakEquivalence_iff _).mp (inferInstance : WeakEquivalence (Subcomplex.fiber f b).ι)
  have hStrict : realizationWeakEquivalences (strictFiberToPathHomotopyFiber f b) :=
    SSet.strictFiberToPathHomotopyFiber_mem_realizationWeakEquivalences f b
  have hComp : realizationWeakEquivalences
      (strictFiberToPathHomotopyFiber f b ≫ pathHomotopyFiberToTotal f b) :=
    (strictFiberToPathHomotopyFiber_toTotal f b).symm ▸ hIncl
  exact realizationWeakEquivalences.of_precomp _ _ hStrict hComp

/-- The original projection from an ending-path fiber over a contractible
Kan target is weak. Contractibility is used only for this neutral geometric lemma. -/
theorem pathHomotopyFiberToTotal_mem_realizationWeakEquivalences_of_point_weak
    {X B : SSet.{u}} [KanComplex X] [KanComplex B] (f : X ⟶ B) (b : B _⦋0⦌)
    (hB : realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from B)) :
    realizationWeakEquivalences (pathHomotopyFiberToTotal f b) := by
  let P : SSet.{u} := Δ[0]
  let q : B ⟶ P := stdSimplex.isTerminalObj₀.from B
  let f' : X ⟶ P := stdSimplex.isTerminalObj₀.from X
  let b' : P _⦋0⦌ := q.app (op ⦋0⦌) b
  let : IsFibrant P :=
    (isFibrant_iff_of_isTerminal (𝟙 P) stdSimplex.isTerminalObj₀).mpr
      (inferInstance : Fibration (𝟙 P))
  let : KanComplex P := inferInstance
  have hAn : SSet.anodyneExtensions.{u} = trivialCofibrations SSet.{u} := by
    rw [SSet.anodyneExtensions_eq_llp_rlp,
      ← SSet.modelCategoryQuillen.fibrations_eq]
    exact fibrations_llp _
  let _ : MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) := by
    rw [← hAn]
    infer_instance
  have hSquare : f ≫ q = (𝟙 X) ≫ f' := stdSimplex.isTerminalObj₀.hom_ext _ _
  let c := pathHomotopyFiberMap (𝟙 X) q hSquare (rfl : q.app (op ⦋0⦌) b = b')
  have hId : realizationWeakEquivalences (𝟙 X) :=
    (weakEquivalence_iff _).mp (inferInstance : WeakEquivalence (𝟙 X))
  have hc : realizationWeakEquivalences c :=
    pathHomotopyFiberMap_mem_realizationWeakEquivalences (𝟙 X) q hSquare rfl hId hB
  have hp : realizationWeakEquivalences (pathHomotopyFiberToTotal f' b') :=
    pointFiberProjection_mem_realizationWeakEquivalences X b'
  have hComp : c ≫ pathHomotopyFiberToTotal f' b' = pathHomotopyFiberToTotal f b :=
    (pathHomotopyFiberMap_toTotal (𝟙 X) q hSquare rfl).trans (Category.comp_id _)
  exact hComp ▸ realizationWeakEquivalences.comp_mem c _ hc hp

namespace KanComplex

/-- The actual native nerve unit induces an equivalence of fundamental
groupoids, derived from its adjunction and the same nerve counit. -/
theorem nativeCoverUnit_mapFundamentalGroupoid_isEquivalence (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (nativeCoverUnit X)).IsEquivalence := by
  let G := SSet.FundamentalGroupoid X
  let B := CategoryTheory.nerve G
  let eta := nativeCoverUnit X
  let F := SSet.mapFundamentalGroupoid eta
  let C := SSet.fundamentalGroupoidNerveCounit G
  let EX := SSet.fundamentalGroupoidNerveEquiv X G
  let EB := SSet.fundamentalGroupoidNerveEquiv B G
  have hPost : EB C = nativeCoverUnit B ≫ CategoryTheory.nerveMap C := by
    simpa only [nativeCoverUnit, Functor.id_comp] using
      (SSet.fundamentalGroupoidNerveEquiv_postcomp
        (𝟭 (SSet.FundamentalGroupoid B)) C)
  have hCounit : EB C = 𝟙 B :=
    hPost.trans (nativeCoverUnit_nerve_comp_counit G)
  have hEq : F ⋙ C = 𝟭 G := by
    apply EX.injective
    calc
      EX (F ⋙ C) = eta ≫ EB C := SSet.fundamentalGroupoidNerveEquiv_precomp eta C
      _ = eta := (congrArg (fun k => eta ≫ k) hCounit).trans (Category.comp_id eta)
      _ = EX (𝟭 G) := rfl
  let : C.IsEquivalence := SSet.fundamentalGroupoidNerveCounit_isEquivalence G
  let : (F ⋙ C).IsEquivalence := by
    rw [hEq]
    infer_instance
  exact Functor.isEquivalence_of_comp_right F C

private abbrev unitBasePoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) _⦋0⦌ :=
  (nativeCoverUnit X).app (op ⦋0⦌) x

private abbrev unitPulledCover (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  pullback (nativeCoverUnit X)
    (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) (unitBasePoint X x))

private def unitCartesianIso (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCover X x ≅ unitPulledCover X x := by
  letI : (SSet.mapFundamentalGroupoid (nativeCoverUnit X)).IsEquivalence :=
    nativeCoverUnit_mapFundamentalGroupoid_isEquivalence X
  let c := nativeCoverCartesianComparison (nativeCoverUnit X) x
  letI : IsIso c := nativeCoverCartesianComparison_isIso (nativeCoverUnit X) x
  exact asIso c

private theorem unitCartesianIso_hom (X : SSet.{u}) (x : X _⦋0⦌) :
    (unitCartesianIso X x).hom = nativeCoverCartesianComparison (nativeCoverUnit X) x := rfl

private theorem unitCartesianIso_inv_fst (X : SSet.{u}) (x : X _⦋0⦌) :
    (unitCartesianIso X x).inv ≫ nativeCoverProjection X x =
      pullback.fst (nativeCoverUnit X)
        (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
            (unitBasePoint X x)) := by
  let c := unitCartesianIso X x
  let q := pullback.fst (nativeCoverUnit X)
    (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) (unitBasePoint X x))
  have h : c.hom ≫ q = nativeCoverProjection X x :=
    (congrArg (fun k => k ≫ q) (unitCartesianIso_hom X x)).trans
      (nativeCoverCartesianComparison_fst (nativeCoverUnit X) x)
  calc
    c.inv ≫ nativeCoverProjection X x = c.inv ≫ (c.hom ≫ q) := congrArg (fun k => c.inv ≫ k) h.symm
    _ = q := (Category.assoc c.inv c.hom q).symm.trans
      ((congrArg (fun k => k ≫ q) c.inv_hom_id).trans (Category.id_comp q))

/-- The actual common ending-path carrier, using the original unit and the
identity point of its original groupoid-base cover. -/
def nativeUnitFiberSpan (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  pathHomotopyFiber
    (pullback.snd (nativeCoverUnit X)
      (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
          (unitBasePoint X x)))
    (nativeCoverIdentityPoint (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        (unitBasePoint X x))

/-- The same original source projection followed by the computed Cartesian inverse. -/
def nativeUnitFiberSpanToCover (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpan X x ⟶ nativeCover X x :=
  pathHomotopyFiberToTotal
    (pullback.snd (nativeCoverUnit X)
      (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
          (unitBasePoint X x)))
    (nativeCoverIdentityPoint (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        (unitBasePoint X x)) ≫
      (unitCartesianIso X x).inv

/-- The existing native-cover path-fiber map, with its original root equation. -/
def nativeUnitFiberSpanToFiber (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpan X x ⟶
      pathHomotopyFiber (nativeCoverUnit X) ((nativeCoverUnit X).app (op ⦋0⦌) x) :=
  nativeCoverBaseChangePathFiberMap (nativeCoverUnit X) (unitBasePoint X x)
    (nativeCoverIdentityPoint (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        (unitBasePoint X x))
    (nativeCoverProjection_identityPoint _ _)

private theorem nativeUnitFiberSpan_projection_computation (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpanToCover X x ≫ nativeCoverProjection X x =
      nativeUnitFiberSpanToFiber X x ≫
        pathHomotopyFiberToTotal (nativeCoverUnit X) ((nativeCoverUnit X).app (op ⦋0⦌) x) := by
  let B : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let eta : X ⟶ B := nativeCoverUnit X
  let a : B _⦋0⦌ := unitBasePoint X x
  let p : nativeCover B a ⟶ B := nativeCoverProjection B a
  let T : SSet.{u} := pullback eta p
  let t : T ⟶ nativeCover B a := pullback.snd eta p
  let b : (nativeCover B a) _⦋0⦌ := nativeCoverIdentityPoint B a
  let Z : SSet.{u} := pathHomotopyFiber t b
  let s : Z ⟶ T := pathHomotopyFiberToTotal t b
  let c : nativeCover X x ≅ T := unitCartesianIso X x
  let px : nativeCover X x ⟶ X := nativeCoverProjection X x
  let q : T ⟶ X := pullback.fst eta p
  let F : SSet.{u} := pathHomotopyFiber eta a
  let r : F ⟶ X := pathHomotopyFiberToTotal eta a
  let m : Z ⟶ F := nativeCoverBaseChangePathFiberMap eta a b
    (nativeCoverProjection_identityPoint B a)
  have hInv : c.inv ≫ px = q := unitCartesianIso_inv_fst X x
  have hMap : m ≫ r = s ≫ q :=
    nativeCoverBaseChangePathFiberMap_toTotal eta a b
      (nativeCoverProjection_identityPoint B a)
  change (s ≫ c.inv) ≫ px = m ≫ r
  exact (Category.assoc s c.inv px).trans
    ((congrArg (fun k : T ⟶ X => s ≫ k) hInv).trans hMap.symm)

/-- Both actual span maps retain the same original projection to X. -/
theorem nativeUnitFiberSpan_projection (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpanToCover X x ≫ nativeCoverProjection X x =
      nativeUnitFiberSpanToFiber X x ≫
        pathHomotopyFiberToTotal (nativeCoverUnit X) ((nativeCoverUnit X).app (op ⦋0⦌) x) :=
  nativeUnitFiberSpan_projection_computation X x

private theorem nativeUnitFiberSpanToFiber_mem_computation
    (X : SSet.{u}) (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToFiber X x) :=
  nativeCoverBaseChangePathFiberMap_mem_realizationWeakEquivalences _ _ _ _

/-- The actual span map to the original unit fiber is the existing canonical
realization weak equivalence; no comparison witness is an input. -/
theorem nativeUnitFiberSpanToFiber_mem_realizationWeakEquivalences
    (X : SSet.{u}) (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToFiber X x) :=
  nativeUnitFiberSpanToFiber_mem_computation X x

private theorem nativeUnitFiberSpanToCover_mem_computation
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToCover X x) := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let a := unitBasePoint X x
  let E := nativeCover B a
  let p := nativeCoverProjection B a
  let T := unitPulledCover X x
  let t : T ⟶ E := pullback.snd (nativeCoverUnit X) p
  let b := nativeCoverIdentityPoint B a
  let : KanComplex B := SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid X)
  let : Fibration p := nativeCoverProjection_fibration B a
  let : KanComplex E := nativeCover_kanComplex B a
  let : KanComplex T := inferInstance
  have hE : realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from E) :=
    nativeCover_nerve_to_point_mem_realizationWeakEquivalences (SSet.FundamentalGroupoid X) a
  have hTotal : realizationWeakEquivalences (pathHomotopyFiberToTotal t b) :=
    pathHomotopyFiberToTotal_mem_realizationWeakEquivalences_of_point_weak t b hE
  have hInv : realizationWeakEquivalences (unitCartesianIso X x).inv :=
    (weakEquivalence_iff _).mp (inferInstance : WeakEquivalence (unitCartesianIso X x).inv)
  exact realizationWeakEquivalences.comp_mem _ _ hTotal hInv

/-- The actual span map to the literal native cover is weak. The intermediate
groupoid-base cover's contractibility is derived from its original unit. -/
theorem nativeUnitFiberSpanToCover_mem_realizationWeakEquivalences
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToCover X x) :=
  nativeUnitFiberSpanToCover_mem_computation X x

/-- The actual span map to the literal strict fiber of the unit's fixed
mapping-path fibration, using the computed generic fiber isomorphism. -/
def nativeUnitFiberSpanToStrictFiber (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpan X x ⟶
      (Subcomplex.fiber (mappingPathTarget (nativeCoverUnit X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x) : SSet.{u}) :=
  nativeUnitFiberSpanToFiber X x ≫
    (pathHomotopyFiberStrictMappingPathIso (nativeCoverUnit X)
      ((nativeCoverUnit X).app (op ⦋0⦌) x)).hom

private theorem nativeUnitFiberSpan_strict_projection_computation
    (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpanToStrictFiber X x ≫
      ((Subcomplex.fiber (mappingPathTarget (nativeCoverUnit X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x)).ι ≫ mappingPathRetract (nativeCoverUnit X)) =
      nativeUnitFiberSpanToCover X x ≫ nativeCoverProjection X x := by
  dsimp only [nativeUnitFiberSpanToStrictFiber]
  rw [Category.assoc, pathHomotopyFiberStrictMappingPathIso_hom_total,
    ← nativeUnitFiberSpan_projection]

/-- The strict fibration fiber and actual native cover comparison have the
same original projection to X. -/
theorem nativeUnitFiberSpan_strict_projection (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeUnitFiberSpanToStrictFiber X x ≫
      ((Subcomplex.fiber (mappingPathTarget (nativeCoverUnit X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x)).ι ≫ mappingPathRetract (nativeCoverUnit X)) =
      nativeUnitFiberSpanToCover X x ≫ nativeCoverProjection X x :=
  nativeUnitFiberSpan_strict_projection_computation X x

private theorem nativeUnitFiberSpanToStrictFiber_mem_computation
    (X : SSet.{u}) (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToStrictFiber X x) := by
  let e : pathHomotopyFiber (nativeCoverUnit X) ((nativeCoverUnit X).app (op ⦋0⦌) x) ≅
      (Subcomplex.fiber (mappingPathTarget (nativeCoverUnit X))
        ((nativeCoverUnit X).app (op ⦋0⦌) x) : SSet.{u}) :=
    pathHomotopyFiberStrictMappingPathIso (nativeCoverUnit X)
      ((nativeCoverUnit X).app (op ⦋0⦌) x)
  have he : realizationWeakEquivalences e.hom :=
    realizationWeakEquivalences.of_isIso e.hom
  exact realizationWeakEquivalences.comp_mem _ _
    (nativeUnitFiberSpanToFiber_mem_realizationWeakEquivalences X x) he

/-- The actual span map to the literal strict fibration fiber is weak. -/
theorem nativeUnitFiberSpanToStrictFiber_mem_realizationWeakEquivalences
    (X : SSet.{u}) (x : X _⦋0⦌) :
    realizationWeakEquivalences (nativeUnitFiberSpanToStrictFiber X x) :=
  nativeUnitFiberSpanToStrictFiber_mem_computation X x

end KanComplex
end SSet
