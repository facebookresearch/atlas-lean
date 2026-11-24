/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.DegreewiseSplit
public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex
public import MathlibExt.Algebra.Homology.MixedComplex.OfBoundaryHomotopy
public import MathlibExt.Algebra.Homology.MixedComplex.ConnesTail
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitalComparison
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Homology.QuasiIso

import Mathlib.Tactic.Abel

/-!
# The Connes homology operator and unital mixed bicomplex

The original Connes zero homotopy supplies B on the original Hochschild
homology. The original component square and unit-preserving map supply its
square-zero and naturality laws. Native translated columns give the mixed
bicomplex. The unital Hochschild comparison uses the bridge,
with an algebra structure reconstructed from the supplied scalar action.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits CategoryTheory.Preadditive HomologicalComplex
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

section CyclicTotalLift

universe x

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The finite diagonal coproducts commute with native universe lifting, without a unit. -/
def cyclicTotalLiftIso.{xTL, uTL, vTL} (k : Type uTL) [CommRing k] (A : Type vTL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{xTL, max uTL vTL} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (cyclicTotal k A) ≅
      HomologicalComplex₂.total (((((ModuleCat.uliftFunctor.{xTL, max uTL vTL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) := by
  let U := ModuleCat.uliftFunctor.{xTL, max uTL vTL} k
  let R : HomologicalComplex₂ (ModuleCat.{max uTL vTL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  exact HomologicalComplex₂.functorTotalIso U R

/-- The total comparison retains each original cyclic-column coprojection. -/
@[reassoc]
theorem map_cyclicInclusion_lift.{xIL, uIL, vIL} (k : Type uIL) [CommRing k]
    (A : Type vIL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (p q n : ℕ) (h : p + q = n) :
    (ModuleCat.uliftFunctor.{xIL, max uIL vIL} k).map
      ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p q n h) ≫
        (cyclicTotalLiftIso.{xIL} k A).hom.f n =
      HomologicalComplex₂.ιTotal (((((ModuleCat.uliftFunctor.{xIL, max uIL vIL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n h := by
  let U := ModuleCat.uliftFunctor.{xIL, max uIL vIL} k
  let R : HomologicalComplex₂ (ModuleCat.{max uIL vIL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  letI : ∀ m, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  change U.map (R.ιTotal (ComplexShape.down ℕ) p q n h) ≫
      (HomologicalComplex₂.functorTotalIsoComponent U R n).hom = _
  exact HomologicalComplex₂.map_ιTotal_functorTotalIsoComponent_hom U R p q n h

/-- Unsupported original cyclic-column coprojections remain zero under the same comparison. -/
@[reassoc]
theorem map_cyclicInclusionOrZero_lift.{xZL, uZL, vZL} (k : Type uZL) [CommRing k]
    (A : Type vZL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (p q n : ℕ) :
    (ModuleCat.uliftFunctor.{xZL, max uZL vZL} k).map
      ((cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p q n) ≫
        (cyclicTotalLiftIso.{xZL} k A).hom.f n =
      HomologicalComplex₂.ιTotalOrZero (((((ModuleCat.uliftFunctor.{xZL, max uZL vZL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n := by
  let U := ModuleCat.uliftFunctor.{xZL, max uZL vZL} k
  let P : HomologicalComplex₂ (ModuleCat.{max xZL uZL vZL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  by_cases h : p + q = n
  · rw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) p q n h,
      P.ιTotalOrZero_eq (ComplexShape.down ℕ) p q n h]
    exact map_cyclicInclusion_lift.{xZL} k A p q n h
  · let R : HomologicalComplex₂ (ModuleCat.{max uZL vZL} k)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
    let T : ChainComplex (ModuleCat.{max xZL uZL vZL} k) ℕ :=
      (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicTotal k A)
    let e : T ≅ P.total (ComplexShape.down ℕ) := cyclicTotalLiftIso.{xZL} k A
    let ι : U.obj ((R.X p).X q) ⟶ T.X n :=
      U.map (R.ιTotalOrZero (ComplexShape.down ℕ) p q n)
    let ρ : (P.X p).X q ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) p q n
    have hι : ι = 0 :=
      (congrArg (fun f : (R.X p).X q ⟶ (cyclicTotal k A).X n => U.map f)
        (R.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p q n h)).trans
          (U.map_zero ((R.X p).X q) ((cyclicTotal k A).X n))
    have hρ : ρ = 0 := P.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p q n h
    change ι ≫ e.hom.f n = ρ
    calc
      _ = (0 : U.obj ((R.X p).X q) ⟶ T.X n) ≫ e.hom.f n :=
        congrArg (fun f : U.obj ((R.X p).X q) ⟶ T.X n => f ≫ e.hom.f n) hι
      _ = 0 := zero_comp
      _ = ρ := hρ.symm

section CyclicTotalMap

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The lifted cyclic total map acts on every original column, including zero coordinates. -/
theorem cyclicBicomplexMap_ιTotalOrZero (f : A →ₙₐ[k] B) (p q n : ℕ) :
    HomologicalComplex₂.ιTotalOrZero
      (((((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n ≫
      (HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)).f n =
        levelMapLift (f : A →ₗ[k] B) q ≫ HomologicalComplex₂.ιTotalOrZero
          (((((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
              (cyclicBicomplex k B))) (ComplexShape.down ℕ) p q n := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k B)
  let φ : PA ⟶ PB := cyclicBicomplexMap f
  let m := HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  change PA.ιTotalOrZero (ComplexShape.down ℕ) p q n ≫ m.f n =
    levelMapLift (f : A →ₗ[k] B) q ≫ PB.ιTotalOrZero (ComplexShape.down ℕ) p q n
  have hι := HomologicalComplex₂.ιTotalOrZero_map PA PB φ (ComplexShape.down ℕ) p q n
  have hφ : (φ.f p).f q = levelMapLift (f : A →ₗ[k] B) q := cyclicBicomplexMap_f_f f p q
  exact hι.trans (congrArg (fun a => a ≫ PB.ιTotalOrZero (ComplexShape.down ℕ) p q n) hφ)

omit [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B] in
/-- The original norm and insertion are natural for any linear map and its insertion vector. -/
theorem normInsertWithMapLift_naturality (f : A →ₗ[k] B) (e : A) (n : ℕ) :
    levelMapLift f n ≫
        (ModuleCat.uliftFunctor.{v, max u w} k).map
          (normMap k B n ≫ extraDegeneracyWith k B (f e) n) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map
          (normMap k A n ≫ extraDegeneracyWith k A e n) ≫ levelMapLift f (n + 1) := by
  apply ModuleCat.hom_ext
  ext x
  let z : A ⊗[k] TensorPower k n A := x.down
  let N := TensorPower.consNorm k A n z
  have hN : TensorPower.consNorm k B n (TensorPower.consLevelMap f n z) =
      TensorPower.consLevelMap f n N := (TensorPower.consNorm_natural f n z).symm
  have hs : (extraDegeneracyWith k B (f e) n).hom (TensorPower.consLevelMap f n N) =
      TensorPower.consLevelMap f (n + 1) ((extraDegeneracyWith k A e n).hom N) :=
    (DFunLike.congr_fun (extraDegeneracyWith_naturality f e n) N).symm
  change ULift.up ((extraDegeneracyWith k B (f e) n).hom
      (TensorPower.consNorm k B n (TensorPower.consLevelMap f n z))) =
    ULift.up (TensorPower.consLevelMap f (n + 1) ((extraDegeneracyWith k A e n).hom N))
  exact congrArg ULift.up ((congrArg (extraDegeneracyWith k B (f e) n).hom hN).trans hs)

end CyclicTotalMap

end CyclicTotalLift

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The Connes component induces degree one on the original regular homology. -/
def connesBoundaryHomology (n : ℕ) :
    (bComplex k A).homology n ⟶ (bComplex k A).homology (n + 1) :=
  (connesBoundaryHomotopy k A).homologyDegreeMap
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- The induced boundary sends cycles through the original Connes component. -/
theorem connesBoundaryHomology_representative (n : ℕ) {X : ModuleCat.{max u v} k}
    (x : X ⟶ (bComplex k A).X n)
    (hx : x ≫ (bComplex k A).d n ((ComplexShape.down ℕ).next n) = 0) :
    ((bComplex k A).liftCycles x _ rfl hx ≫ (bComplex k A).homologyπ n) ≫
        connesBoundaryHomology k A n =
      (bComplex k A).liftCycles (x ≫ connesBoundary k A n) n
        ((ComplexShape.down ℕ).next_eq' (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n))
        (by
          simpa only [connesBoundaryHomotopy_hom] using
            ((connesBoundaryHomotopy k A).homologyDegreeMap_isCycle
              (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) x hx)) ≫
        (bComplex k A).homologyπ (n + 1) := by
  simpa only [connesBoundaryHomology, connesBoundaryHomotopy_hom] using
    (connesBoundaryHomotopy k A).homologyDegreeMap_cycle_representative
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) x hx

/-- The component square-zero law descends to the original homology objects. -/
theorem connesBoundaryHomology_square (n : ℕ) :
    connesBoundaryHomology k A n ≫ connesBoundaryHomology k A (n + 1) = 0 := by
  apply Homotopy.homologyDegreeMap_comp_eq_zero
    (connesBoundaryHomotopy k A)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))
    (connesBoundaryHomotopy k A)
  simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n

/-- Native universe lifting carries the same secondary homotopy. -/
def connesBoundaryHomotopyLift :
    Homotopy
      (0 : ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (bComplex k A) ⟶
          ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (bComplex k A)) 0 where
  hom := ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
    (connesBoundaryHomotopy k A)).hom
  zero := ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
    (connesBoundaryHomotopy k A)).zero
  comm n := by
    simpa only [Functor.map_zero, HomologicalComplex.zero_f_apply] using
      ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
        (connesBoundaryHomotopy k A)).comm n

/-- Native lifting retains the original Connes component, with no supplied comparison. -/
@[simp]
theorem connesBoundaryHomotopyLift_hom (n : ℕ) :
    (connesBoundaryHomotopyLift.{u, v, w} k A).hom n (n + 1) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map (connesBoundary k A n) := by
  change (ModuleCat.uliftFunctor.{w, max u v} k).map
    ((connesBoundaryHomotopy k A).hom n (n + 1)) = _
  rw [connesBoundaryHomotopy_hom]

section Naturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Independent-world maps induce the original full-boundary map after native lifting. -/
def bComplexMapLift (f : A →ₙₐ[k] B) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k A) ⟶
    ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k B) :=
  ChainComplex.ofHom (levelMapLift (f : A →ₗ[k] B)) (fun n => by
    apply ModuleCat.hom_ext
    ext x
    change ULift.up (((bComplex k B).d (n + 1) n).hom
        (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1) x.down)) =
      ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) n
        (((bComplex k A).d (n + 1) n).hom x.down))
    exact congrArg ULift.up (DFunLike.congr_fun (bComplex_d_natural f n) x.down).symm)

/-- The lifted chain map keeps the original tensor-level map. -/
@[simp]
theorem bComplexMapLift_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (bComplexMapLift f).f n = levelMapLift (f : A →ₗ[k] B) n := rfl

/-- Actual unit-preserving maps intertwine the original lifted Connes components. -/
theorem bComplexMapLift_boundary (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (bComplexMapLift f).f n ≫ (connesBoundaryHomotopyLift.{u, w, v} k B).hom n (n + 1) =
      (connesBoundaryHomotopyLift.{u, v, w} k A).hom n (n + 1) ≫
        (bComplexMapLift f).f (n + 1) := by
  rw [connesBoundaryHomotopyLift_hom, connesBoundaryHomotopyLift_hom,
    bComplexMapLift_f, bComplexMapLift_f]
  apply ModuleCat.hom_ext
  ext x
  change ULift.up ((connesBoundary k B n).hom
      (TensorPower.consLevelMap (f : A →ₗ[k] B) n x.down)) =
    ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)
      ((connesBoundary k A n).hom x.down))
  exact congrArg ULift.up (DFunLike.congr_fun (connesBoundary_naturality f hOne n) x.down).symm

/-- Actual unit-preserving maps intertwine induced B in independent raw module worlds. -/
theorem connesBoundaryHomology_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    homologyMap (bComplexMapLift f) n ≫
        (connesBoundaryHomotopyLift.{u, w, v} k B).homologyDegreeMap
          (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) =
      (connesBoundaryHomotopyLift.{u, v, w} k A).homologyDegreeMap
          (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) ≫
        homologyMap (bComplexMapLift f) (n + 1) := by
  apply Homotopy.homologyDegreeMap_naturality_square
    (connesBoundaryHomotopyLift.{u, v, w} k A)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
    (connesBoundaryHomotopyLift.{u, w, v} k B) (bComplexMapLift f) (bComplexMapLift f)
  exact bComplexMapLift_boundary f hOne n

end Naturality

/-- The algebra structure is from and retains the supplied ground scalar action. -/
abbrev regularAlgebra : Algebra k A :=
  Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)

/-- The original regular complex uses the unital Hochschild bridge. -/
def regularUnitalComplexIso :
    letI := regularAlgebra k A
    bComplex k A ≅ ModuleCat.Algebra.Hochschild.chainComplex k A A := by
  letI := regularAlgebra k A
  let e := complexIsoUnital (k := k) (A := A) (M := A)
  change bComplex k A ≅ ModuleCat.Algebra.Hochschild.chainComplex k A A at e
  exact e

/-- Actual Connes B on the unital Hochschild homology, through the bridge. -/
def connesBoundaryHomologyUnital (n : ℕ) :
    letI := regularAlgebra k A
    (ModuleCat.Algebra.Hochschild.chainComplex k A A).homology n ⟶
      (ModuleCat.Algebra.Hochschild.chainComplex k A A).homology (n + 1) := by
  letI := regularAlgebra k A
  let e := regularUnitalComplexIso k A
  exact (homologyMapIso e n).inv ≫ connesBoundaryHomology k A n ≫
    (homologyMapIso e (n + 1)).hom

/-- The original b/B data construct the canonical mixed complex. -/
def connesMixedComplexModel : MixedComplex (ModuleCat.{max u v} k) :=
  MixedComplex.ofBoundaryHomotopy (bComplex k A) (connesBoundaryHomotopy k A)
    (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)

/-- The canonical object retains the original regular b-complex. -/
@[simp]
theorem connesMixedComplexModel_underlying :
    (connesMixedComplexModel k A).underlying = bComplex k A := rfl

/-- Its canonical mixed operator is the original N-insertion-(1-t) map. -/
@[simp]
theorem connesMixedComplexModel_B (n : ℕ) :
    (connesMixedComplexModel k A).B n = connesBoundary k A n := connesBoundaryHomotopy_hom k A n

/-- The component-characterized Connes data are from the canonical mixed object. -/
def connesMixedConnesDoubleData : MixedComplex.ConnesDoubleData (connesMixedComplexModel k A) :=
  MixedComplex.ofBoundaryHomotopyConnesDoubleData (bComplex k A) (connesBoundaryHomotopy k A)
    (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)

/-- The generic cyclic data use the canonical mixed object and its comparisons. -/
def connesMixedGenericCyclicData : MixedComplex.GenericMixedCyclicData (connesMixedComplexModel k A) :=
  (connesMixedComplexModel k A).connesCyclicData

/-- The unital mixed bicomplex is formed from the original b and Connes B. -/
def connesMixedBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (connesMixedConnesDoubleData k A).K

/-- Canonical Connes packaging retains the entire original homotopy-based bicomplex. -/
theorem connesMixedBicomplex_eq_original :
    connesMixedBicomplex k A = ChainComplex.mixedBicomplex (bComplex k A) (connesBoundaryHomotopy k A)
      (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n) := rfl

/-- The generic cyclic-data model is the same original bicomplex. -/
theorem connesMixedGenericCyclicData_model_K :
    (connesMixedGenericCyclicData k A).model.K = connesMixedBicomplex k A :=
  MixedComplex.ofBoundaryHomotopy_connesBicomplex (bComplex k A)
    (connesBoundaryHomotopy k A) (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r)

/-- The bottom cell in every translated column retains the original X0. -/
def connesMixedBottomIso (p : ℕ) :
    ((connesMixedBicomplex k A).X p).X p ≅ chainLevel k A A 0 :=
  ChainComplex.mixedColumnIso (bComplex k A) p 0 p (Nat.zero_add p)

/-- Every supported mixed cell has the original printed degree q-p. -/
def connesMixedCellIso (p q : ℕ) (hpq : p ≤ q) :
    ((connesMixedBicomplex k A).X p).X q ≅ chainLevel k A A (q - p) :=
  ChainComplex.mixedBicomplexCellIso (bComplex k A) (connesBoundaryHomotopy k A)
    (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r) p q hpq

/-- Native finite-diagonal totalization is the mixed total complex. -/
abbrev connesMixedTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (connesMixedBicomplex k A).total (ComplexShape.down ℕ)

/-- A supported original mixed cell has its total inclusion. -/
def connesMixedInclusion (p q : ℕ) (hpq : p ≤ q) :
    chainLevel k A A (q - p) ⟶ (connesMixedTotal k A).X (p + q) :=
  (connesMixedCellIso k A p q hpq).inv ≫
    (connesMixedBicomplex k A).ιTotal (ComplexShape.down ℕ) p q (p + q) rfl

/-- The native vertical sign is exactly the original positive Hochschild boundary. -/
theorem connesMixedTotal_vertical (p n : ℕ) :
    (ComplexShape.down ℕ).ε p •
        ((connesMixedBicomplex k A).X p).d (n + 1 + p) (n + p) =
      (ChainComplex.mixedColumnIso (bComplex k A) p (n + 1) (n + 1 + p) rfl).hom ≫
        (bComplex k A).d (n + 1) n ≫
          (ChainComplex.mixedColumnIso (bComplex k A) p n (n + p) rfl).inv :=
  ChainComplex.mixedBicomplex_total_vertical (bComplex k A) (connesBoundaryHomotopy k A)
    (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r) p (n + 1) n
    (n + 1 + p) (n + p) rfl rfl

/-- The odd quotient is the graded family of translated minus-b-prime columns. -/
def connesOddFamily : ChainComplex (GradedObject ℕ (ModuleCat.{max u v} k)) ℕ where
  X n j := (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).X n
  d n m j := (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).d n m
  shape n m h := by
    funext j
    exact (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).shape n m h
  d_comp_d' n m l _ _ := by
    funext j
    exact (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).d_comp_d n m l

/-- Every odd column contracts by the transported original unit insertion. -/
def connesOddFamilyContraction : Homotopy (𝟙 (connesOddFamily k A)) 0 where
  hom n m j :=
    (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).hom n m
  zero n m hnm := by
    funext j
    exact (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).zero n m hnm
  comm n := by
    funext j
    exact (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).comm n

/-- The quotient complex is the native coproduct of the odd translated columns. -/
abbrev connesOddTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesOddFamily k A)

/-- The native additive coproduct functor transports the quotient contraction. -/
def connesOddContraction : Homotopy (𝟙 (connesOddTotal k A)) 0 where
  hom := ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomotopy
    (connesOddFamilyContraction k A)).hom
  zero := ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomotopy
    (connesOddFamilyContraction k A)).zero
  comm n := by
    let F := GradedObject.total ℕ (ModuleCat.{max u v} k)
    let U := F.mapHomologicalComplex (ComplexShape.down ℕ)
    let K : ChainComplex (GradedObject ℕ (ModuleCat.{max u v} k)) ℕ := connesOddFamily k A
    let L : ChainComplex (ModuleCat.{max u v} k) ℕ := connesOddTotal k A
    let H : Homotopy (U.map (𝟙 K)) (U.map (0 : K ⟶ K)) :=
      F.mapHomotopy (connesOddFamilyContraction k A)
    let a : ∀ i j : ℕ, L.X i ⟶ L.X j := H.hom
    have hId : U.map (𝟙 K) = 𝟙 L := U.map_id K
    have hZero : U.map (0 : K ⟶ K) = (0 : L ⟶ L) := U.map_zero K K
    have hIdF : (U.map (𝟙 K)).f n = (𝟙 L : L ⟶ L).f n :=
      congrArg (fun f : L ⟶ L => f.f n) hId
    have hZeroF : (U.map (0 : K ⟶ K)).f n = (0 : L ⟶ L).f n :=
      congrArg (fun f : L ⟶ L => f.f n) hZero
    change (𝟙 L : L ⟶ L).f n = dNext n a + prevD n a + (0 : L ⟶ L).f n
    exact hIdF.symm.trans ((H.comm n).trans
      (congrArg (fun z : L.X n ⟶ L.X n => dNext n a + prevD n a + z) hZeroF))

/-- Each supported original odd level has its quotient coprojection. -/
def connesOddInclusion (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) r n h).inv ≫
    Sigma.ι ((connesOddFamily k A).X n) j

/-- Supported original odd levels detect equality of morphisms from the quotient. -/
theorem connesOddTotal_hom_ext {X : ModuleCat.{max u v} k} (n : ℕ)
    {f g : (connesOddTotal k A).X n ⟶ X}
    (h : ∀ j r (hr : r + (2 * j + 1) = n),
      connesOddInclusion k A j r n hr ≫ f = connesOddInclusion k A j r n hr ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro j
  by_cases hj : 2 * j + 1 ≤ n
  · let r := n - (2 * j + 1)
    have hr : r + (2 * j + 1) = n := Nat.sub_add_cancel hj
    let e : ((connesOddFamily k A).X n) j ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) r n hr
    let ι : ((connesOddFamily k A).X n) j ⟶ (connesOddTotal k A).X n :=
      CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X n) j
    apply (cancel_epi e.inv).1
    have hh : (e.inv ≫ ι) ≫ f = (e.inv ≫ ι) ≫ g := h j r hr
    change e.inv ≫ (ι ≫ f) = e.inv ≫ (ι ≫ g)
    exact (Category.assoc e.inv ι f).symm.trans (hh.trans (Category.assoc e.inv ι g))
  · exact (ChainComplex.mixedColumn_isZero (bPrimeComplex k A) (2 * j + 1) n
      (by omega)).eq_of_src _ _

/-- The quotient's original odd-column differential is the printed minus-b-prime. -/
theorem connesOddInclusion_d (j r n m : ℕ)
    (hn : (r + 1) + (2 * j + 1) = n) (hm : r + (2 * j + 1) = m) :
    connesOddInclusion k A j (r + 1) n hn ≫ (connesOddTotal k A).d n m =
      -(bPrimeComplex k A).d (r + 1) r ≫ connesOddInclusion k A j r m hm := by
  let K := bPrimeComplex k A
  let T := connesOddTotal k A
  let e₁ : ((connesOddFamily k A).X n) j ≅ chainLevel k A A (r + 1) :=
    ChainComplex.mixedColumnIso K (2 * j + 1) (r + 1) n hn
  let e₀ : ((connesOddFamily k A).X m) j ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso K (2 * j + 1) r m hm
  let ι₁ : ((connesOddFamily k A).X n) j ⟶ T.X n :=
    CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X n) j
  let ι₀ : ((connesOddFamily k A).X m) j ⟶ T.X m :=
    CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X m) j
  let δ : ∀ a : ℕ, ((connesOddFamily k A).X n) a ⟶ ((connesOddFamily k A).X m) a :=
    (connesOddFamily k A).d n m
  let v : ((connesOddFamily k A).X n) j ⟶ ((connesOddFamily k A).X m) j := δ j
  let D : T.X n ⟶ T.X m := T.d n m
  let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := K.d (r + 1) r
  have hι : ι₁ ≫ D = v ≫ ι₀ := CategoryTheory.Limits.Sigma.ι_map δ j
  have hOdd : Odd (2 * j + 1) := ⟨j, by omega⟩
  have hv : v = e₁.hom ≫ (-d) ≫ e₀.inv := by
    have hD : v = e₁.hom ≫ (((-1 : ℤˣ) ^ (2 * j + 1)) • d) ≫ e₀.inv := by
      change (ChainComplex.mixedColumn K (2 * j + 1)).d n m = _
      exact ChainComplex.mixedColumn_d_eq K (2 * j + 1) (r + 1) r n m hn hm
    have hsign : ((-1 : ℤˣ) ^ (2 * j + 1)) • d = -d := by
      erw [hOdd.neg_one_pow]
      simp only [Units.neg_smul, one_smul]
    exact hD.trans (congrArg (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A r =>
      e₁.hom ≫ f ≫ e₀.inv) hsign)
  change (e₁.inv ≫ ι₁) ≫ D = -(d ≫ e₀.inv ≫ ι₀)
  calc
    _ = e₁.inv ≫ (ι₁ ≫ D) := Category.assoc _ _ _
    _ = e₁.inv ≫ (v ≫ ι₀) :=
      congrArg (fun f : ((connesOddFamily k A).X n) j ⟶ T.X m => e₁.inv ≫ f) hι
    _ = e₁.inv ≫ ((e₁.hom ≫ (-d) ≫ e₀.inv) ≫ ι₀) :=
      congrArg (fun f : ((connesOddFamily k A).X n) j ⟶ ((connesOddFamily k A).X m) j =>
        e₁.inv ≫ f ≫ ι₀) hv
    _ = -(d ≫ e₀.inv ≫ ι₀) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.neg_comp, Preadditive.comp_neg]

/-- Original even coordinates have the native mixed-total coprojection. -/
def mixedLevelInclusion (p r n : ℕ) (h : 2 * p + r = n) :
    chainLevel k A A r ⟶ (connesMixedTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (connesMixedBicomplex k A).ιTotal (ComplexShape.down ℕ) p (r + p) n (by
      change p + (r + p) = n
      omega)

/-- The same original mixed-level coprojection is zero when its total degree does not match. -/
def mixedLevelInclusionOrZero (p r n : ℕ) :
    chainLevel k A A r ⟶ (connesMixedTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (connesMixedBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p (r + p) n

/-- Supported total coordinates agree with the original-level inclusion. -/
theorem mixedLevelInclusionOrZero_eq (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusionOrZero k A p r n = mixedLevelInclusion k A p r n h := by
  unfold mixedLevelInclusionOrZero mixedLevelInclusion
  erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
    change p + (r + p) = n
    omega)]

/-- Supported original even levels detect equality of maps from the mixed total. -/
theorem connesMixedTotal_hom_ext {X : ModuleCat.{max u v} k} (n : ℕ)
    {f g : (connesMixedTotal k A).X n ⟶ X}
    (h : ∀ p r (hr : 2 * p + r = n),
      mixedLevelInclusion k A p r n hr ≫ f = mixedLevelInclusion k A p r n hr ≫ g) :
    f = g := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hn
  by_cases hpq : p ≤ q
  · obtain ⟨r, hrq⟩ : ∃ r : ℕ, q = r + p :=
      ⟨q - p, (Nat.sub_add_cancel hpq).symm⟩
    subst q
    have hr : 2 * p + r = n := by
      change p + (r + p) = n at hn
      omega
    let B := connesMixedBicomplex k A
    let e : (B.X p).X (r + p) ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
    let i : (B.X p).X (r + p) ⟶ (connesMixedTotal k A).X n :=
      B.ιTotal (ComplexShape.down ℕ) p (r + p) n hn
    apply (cancel_epi e.inv).1
    have hv : (e.inv ≫ i) ≫ f = (e.inv ≫ i) ≫ g := h p r hr
    exact (Category.assoc e.inv i f).symm.trans (hv.trans (Category.assoc e.inv i g))
  · let B := connesMixedBicomplex k A
    have hSquare : ∀ m : ℕ,
        (connesBoundaryHomotopy k A).hom m (m + 1) ≫
          (connesBoundaryHomotopy k A).hom (m + 1) (m + 2) = 0 := fun m => by
      simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A m
    have hZero : IsZero ((B.X p).X q) :=
      ChainComplex.mixedBicomplex_isZero_cell (bComplex k A)
        (connesBoundaryHomotopy k A) hSquare p q (by omega)
    let mf : (B.X p).X q ⟶ X := B.ιTotal (ComplexShape.down ℕ) p q n hn ≫ f
    let mg : (B.X p).X q ⟶ X := B.ιTotal (ComplexShape.down ℕ) p q n hn ≫ g
    exact hZero.eq_of_src mf mg

/-- An odd coprojection with an unmatched degree is the zero morphism. -/
def connesOddInclusionOrZero (j r n : ℕ) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  if h : r + (2 * j + 1) = n then connesOddInclusion k A j r n h else 0

/-- Matching odd degrees recover the original quotient coprojection. -/
theorem connesOddInclusionOrZero_eq (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    connesOddInclusionOrZero k A j r n = connesOddInclusion k A j r n h := dif_pos h

/-- The even coordinate projection preserves exactly the original mixed level. -/
def mixedEvenProjection (n : ℕ) :
    (cyclicTotal k A).X n ⟶ (connesMixedTotal k A).X n :=
  (cyclicBicomplex k A).totalDesc (fun c r hn =>
    if hc : Even c then mixedLevelInclusionOrZero k A (c / 2) r n else 0)

/-- Even cyclic coordinates project to their mixed-total coordinate. -/
theorem mixedEvenProjection_even (p r n : ℕ) (h : 2 * p + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫
        mixedEvenProjection k A n = mixedLevelInclusion k A p r n h := by
  have hp : Even (2 * p) := ⟨p, by omega⟩
  have hDiv : (2 * p) / 2 = p := by omega
  erw [mixedEvenProjection, HomologicalComplex₂.ι_totalDesc]
  simp only [dif_pos hp, if_pos hp, hDiv, mixedLevelInclusionOrZero_eq k A p r n h]
  all_goals first | exact dif_pos hp | exact if_pos hp

/-- Original odd cyclic coordinates vanish under the even projection. -/
theorem mixedEvenProjection_odd (j r n : ℕ) (h : 2 * j + 1 + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * j + 1) r n h ≫
        mixedEvenProjection k A n = 0 := by
  have hj : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  erw [mixedEvenProjection, HomologicalComplex₂.ι_totalDesc]
  exact dif_neg hj

/-- The original odd coordinate is inserted into its cyclic-total column. -/
def connesOddSection (n : ℕ) : (connesOddTotal k A).X n ⟶ (cyclicTotal k A).X n :=
  Sigma.desc (fun j =>
    if hj : 2 * j + 1 ≤ n then
      (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1)
        (n - (2 * j + 1)) n (Nat.sub_add_cancel hj)).hom ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * j + 1) (n - (2 * j + 1)) n
    else 0)

/-- The odd section has exactly its original cyclic-column coprojection. -/
theorem connesOddInclusion_section (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    connesOddInclusion k A j r n h ≫ connesOddSection k A n =
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n := by
  have hj : 2 * j + 1 ≤ n := by omega
  have hr : n - (2 * j + 1) = r := by omega
  subst r
  let F : ℕ → ModuleCat.{max u v} k := (connesOddFamily k A).X n
  let T := connesOddTotal k A
  let e : F j ≅ chainLevel k A A (n - (2 * j + 1)) :=
    ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1)
      (n - (2 * j + 1)) n h
  let ι : F j ⟶ T.X n := Sigma.ι F j
  let s : T.X n ⟶ (cyclicTotal k A).X n := connesOddSection k A n
  let v : chainLevel k A A (n - (2 * j + 1)) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
      (2 * j + 1) (n - (2 * j + 1)) n
  have hι : ι ≫ s = e.hom ≫ v := by
    dsimp only [ι, s, connesOddSection]
    erw [Sigma.ι_desc]
    exact dif_pos hj
  change (e.inv ≫ ι) ≫ s = v
  calc
    (e.inv ≫ ι) ≫ s = e.inv ≫ (ι ≫ s) := Category.assoc _ _ _
    _ = e.inv ≫ (e.hom ≫ v) :=
      congrArg (fun a : F j ⟶ (cyclicTotal k A).X n => e.inv ≫ a) hι
    _ = v := e.inv_hom_id_assoc v


/-- Zero and matching odd coprojections both retain the same original cyclic coordinate. -/
theorem connesOddInclusionOrZero_section (j r n : ℕ) :
    connesOddInclusionOrZero k A j r n ≫ connesOddSection k A n =
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n := by
  by_cases h : r + (2 * j + 1) = n
  · erw [connesOddInclusionOrZero_eq k A j r n h, connesOddInclusion_section]
  · erw [connesOddInclusionOrZero, dif_neg h, zero_comp,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change 2 * j + 1 + r ≠ n
        omega)] <;> rfl

/-- The positive printed level image omits only the nonexistent negative column at p=0. -/
def mixedToCyclicLevelImage (p r n : ℕ) :
    chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
  let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
    if p = 0 then 0 else
      normMap k A r ≫ extraDegeneracy k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  x + y

/-- The positive printed inclusion on each total degree uses N followed by s. -/
def mixedToCyclicComponent (n : ℕ) :
    (connesMixedTotal k A).X n ⟶ (cyclicTotal k A).X n :=
  (connesMixedBicomplex k A).totalDesc (fun p q hn =>
    if hpq : p ≤ q then
      (connesMixedCellIso k A p q hpq).hom ≫ mixedToCyclicLevelImage k A p (q - p) n
    else 0)

theorem mixedToCyclicComponent_levelImage (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusion k A p r n h ≫ mixedToCyclicComponent k A n =
      mixedToCyclicLevelImage k A p r n := by
  have hpq : p ≤ r + p := by omega
  have hr : r + p - p = r := Nat.add_sub_cancel r p
  let K := bComplex k A
  let e : ((connesMixedBicomplex k A).X p).X (r + p) ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso K p r (r + p) rfl
  let F : chainLevel k A A r ⟶ (cyclicTotal k A).X n := mixedToCyclicLevelImage k A p r n
  have hCell : (connesMixedCellIso k A p (r + p) hpq).hom ≫
      mixedToCyclicLevelImage k A p (r + p - p) n = e.hom ≫ F := by
    change (ChainComplex.mixedColumnIso K p (r + p - p) (r + p)
      (Nat.sub_add_cancel hpq)).hom ≫ mixedToCyclicLevelImage k A p (r + p - p) n = _
    have hCompare : ∀ (t : ℕ) (ht : t + p = r + p), t = r →
        (ChainComplex.mixedColumnIso K p t (r + p) ht).hom ≫
          mixedToCyclicLevelImage k A p t n = e.hom ≫ F := by
      intro t ht he
      cases he
      rfl
    exact hCompare (r + p - p) (Nat.sub_add_cancel hpq) hr
  unfold mixedLevelInclusion mixedToCyclicComponent
  erw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  calc
    _ = e.inv ≫ ((connesMixedCellIso k A p (r + p) hpq).hom ≫
        mixedToCyclicLevelImage k A p (r + p - p) n) :=
      congrArg (fun f : ((connesMixedBicomplex k A).X p).X (r + p) ⟶ (cyclicTotal k A).X n =>
        e.inv ≫ f) (dite_eq_left hpq)
    _ = e.inv ≫ (e.hom ≫ F) :=
      congrArg (fun f : ((connesMixedBicomplex k A).X p).X (r + p) ⟶ (cyclicTotal k A).X n =>
        e.inv ≫ f) hCell
    _ = F := e.inv_hom_id_assoc F

/-- The original mixed coordinate is sent by the positive x plus sN formula. -/
theorem mixedToCyclicComponent_inclusion (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusion k A p r n h ≫ mixedToCyclicComponent k A n =
      (let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
       let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          normMap k A r ≫ extraDegeneracy k A r ≫
            (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
       x + y) := by
  erw [mixedToCyclicComponent_levelImage]
  by_cases hp : p = 0
  · subst p
    let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * 0) r n
    let i : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * 0 - 1) (r + 1) n
    let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
      normMap k A r ≫ extraDegeneracy k A r ≫ i
    have hi : i = 0 := HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
      change 2 * 0 - 1 + (r + 1) ≠ n
      omega)
    have hy : y = 0 := (Category.assoc (normMap k A r) (extraDegeneracy k A r) i).symm.trans
      ((congrArg (fun f : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n =>
        (normMap k A r ≫ extraDegeneracy k A r) ≫ f) hi).trans comp_zero)
    change x + 0 = x + y
    exact congrArg (fun f : chainLevel k A A r ⟶ (cyclicTotal k A).X n => x + f) hy.symm
  · exact by simp only [mixedToCyclicLevelImage, if_neg hp]

/-- The level image is zero outside its mixed-total degree. -/
theorem mixedToCyclicLevelImage_eq_zero (p r n : ℕ) (h : 2 * p + r ≠ n) :
    mixedToCyclicLevelImage k A p r n = 0 := by
  have hz : (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n = 0 :=
    HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h
  by_cases hp : p = 0
  · simp only [mixedToCyclicLevelImage, if_pos hp, hz, add_zero]
    exact zero_add (0 : chainLevel k A A r ⟶ (cyclicTotal k A).X n)
  · have hz' : (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n = 0 :=
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change 2 * p - 1 + (r + 1) ≠ n
        omega)
    simp only [mixedToCyclicLevelImage, if_neg hp, hz, hz', comp_zero, add_zero]
    let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let Z := (cyclicTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    have hzero : N ≫ S ≫ (0 : Y ⟶ Z) = 0 :=
      (Category.assoc N S (0 : Y ⟶ Z)).symm.trans comp_zero
    change (0 : X ⟶ Z) + N ≫ S ≫ (0 : Y ⟶ Z) = 0
    exact (congrArg (fun f : X ⟶ Z => (0 : X ⟶ Z) + f) hzero).trans (zero_add 0)

/-- Both matching and zero native mixed coprojections retain the level image. -/
theorem mixedToCyclicComponent_inclusionOrZero (p r n : ℕ) :
    mixedLevelInclusionOrZero k A p r n ≫ mixedToCyclicComponent k A n =
      mixedToCyclicLevelImage k A p r n := by
  by_cases h : 2 * p + r = n
  · erw [mixedLevelInclusionOrZero_eq k A p r n h, mixedToCyclicComponent_levelImage]
  · have hz : mixedLevelInclusionOrZero k A p r n = 0 := by
      unfold mixedLevelInclusionOrZero
      erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change p + (r + p) ≠ n
        omega), comp_zero]
    erw [hz, zero_comp, mixedToCyclicLevelImage_eq_zero k A p r n h]

/-- The even quotient image omits the nonexistent preceding odd column at p=0. -/
def cyclicToOddEvenImage (p r n : ℕ) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  if p = 0 then 0 else
    -(normMap k A r ≫ extraDegeneracy k A r ≫
      connesOddInclusionOrZero k A (p - 1) (r + 1) n)

/-- The quotient is (-sN,id) in the original even/odd coordinates. -/
def cyclicToOddComponent (n : ℕ) :
    (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
  (cyclicBicomplex k A).totalDesc (fun c r hn =>
    if hc : Even c then cyclicToOddEvenImage k A (c / 2) r n
    else connesOddInclusionOrZero k A (c / 2) r n)

/-- The quotient sends an original even coordinate through minus sN. -/
theorem cyclicToOddComponent_even (p r n : ℕ) (h : 2 * p + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫
        cyclicToOddComponent k A n =
      -(normMap k A r ≫ extraDegeneracy k A r ≫
        connesOddInclusionOrZero k A (p - 1) (r + 1) n) := by
  have hp : Even (2 * p) := ⟨p, by omega⟩
  have hDiv : (2 * p) / 2 = p := by omega
  erw [cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_left hp, hDiv]
  by_cases hp0 : p = 0
  · subst p
    let i : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n :=
      connesOddInclusionOrZero k A (0 - 1) (r + 1) n
    let Y : chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
      normMap k A r ≫ extraDegeneracy k A r ≫ i
    have hi : i = 0 := by
      unfold i connesOddInclusionOrZero
      exact dite_eq_right (by omega)
    have hY : Y = 0 := (Category.assoc (normMap k A r) (extraDegeneracy k A r) i).symm.trans
      ((congrArg (fun f : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n =>
        (normMap k A r ≫ extraDegeneracy k A r) ≫ f) hi).trans comp_zero)
    change (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) = -Y
    exact ((congrArg (fun f : chainLevel k A A r ⟶ (connesOddTotal k A).X n => -f) hY).trans
      neg_zero).symm
  · change (if p = 0 then (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) else
      -(normMap k A r ≫ extraDegeneracy k A r ≫
        connesOddInclusionOrZero k A (p - 1) (r + 1) n)) = _
    exact if_neg hp0

/-- The quotient sends an original odd coordinate by its identity coordinate. -/
theorem cyclicToOddComponent_odd (j r n : ℕ) (h : 2 * j + 1 + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * j + 1) r n h ≫
        cyclicToOddComponent k A n = connesOddInclusion k A j r n (by omega) := by
  have hj : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  have hDiv : (2 * j + 1) / 2 = j := by omega
  erw [cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_right hj, hDiv]
  exact connesOddInclusionOrZero_eq k A j r n (by omega)

/-- The even quotient level image is zero outside its original total degree. -/
theorem cyclicToOddEvenImage_eq_zero (p r n : ℕ) (h : 2 * p + r ≠ n) :
    cyclicToOddEvenImage k A p r n = 0 := by
  by_cases hp : p = 0
  · simp only [cyclicToOddEvenImage, if_pos hp]
  · have hz : connesOddInclusionOrZero k A (p - 1) (r + 1) n = 0 := by
      unfold connesOddInclusionOrZero
      erw [dif_neg (by omega)]
    simp only [cyclicToOddEvenImage, if_neg hp, hz, comp_zero, neg_zero]

/-- Zero and matching even coprojections both retain the even quotient image. -/
theorem cyclicToOddComponent_evenOrZero (p r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n ≫
        cyclicToOddComponent k A n = cyclicToOddEvenImage k A p r n := by
  by_cases h : 2 * p + r = n
  · have hp : Even (2 * p) := ⟨p, by omega⟩
    have hDiv : (2 * p) / 2 = p := by omega
    erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_left hp, hDiv]
  · erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp,
      cyclicToOddEvenImage_eq_zero k A p r n h]
    change (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) = 0
    rfl

/-- Zero and matching odd coprojections both retain the original quotient coordinate. -/
theorem cyclicToOddComponent_oddOrZero (j r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n ≫
        cyclicToOddComponent k A n = connesOddInclusionOrZero k A j r n := by
  by_cases h : 2 * j + 1 + r = n
  · erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      cyclicToOddComponent_odd k A j r n h, connesOddInclusionOrZero_eq k A j r n (by omega)]
  · erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp]
    have hz : r + (2 * j + 1) ≠ n := by omega
    have hi : connesOddInclusionOrZero k A j r n = 0 := by
      change (if hs : r + (2 * j + 1) = n then connesOddInclusion k A j r n hs else
        (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n)) = 0
      exact dite_eq_right hz
    exact hi.symm
theorem cyclic_d₁_even (p r m : ℕ) :
    (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) (2 * p) r m =
      if p = 0 then 0 else normMap k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) r m := by
  by_cases hp : p = 0
  · subst p
    erw [if_pos rfl]
    exact (cyclicBicomplex k A).d₁_eq_zero (ComplexShape.down ℕ) 0 r m
      (by simp [ComplexShape.down_Rel])
  · erw [if_neg hp, (cyclicBicomplex k A).d₁_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (2 * p) (2 * p - 1) from by
        change 2 * p - 1 + 1 = 2 * p
        omega) r m]
    have hc : ¬ Even (2 * p - 1) := by rintro ⟨a, ha⟩; omega
    have hpred : (2 * p - 1) + 1 = 2 * p := by omega
    have hField := cyclicBicomplex_horizontal k A (2 * p - 1) r
    erw [hpred, if_neg hc] at hField
    change (1 : ℤˣ) •
      (((cyclicBicomplex k A).d (2 * p) (2 * p - 1)).f r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) r m) = _
    erw [one_smul, hField] <;> rfl

theorem cyclic_d₁_odd (j r m : ℕ) :
    (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) (2 * j + 1) r m =
      (𝟙 (chainLevel k A A r) - cyclicMap k A r) ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) r m := by
  erw [(cyclicBicomplex k A).d₁_eq' (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (2 * j + 1) (2 * j) from rfl) r m]
  have hc : Even (2 * j) := ⟨j, by omega⟩
  have hField := cyclicBicomplex_horizontal k A (2 * j) r
  erw [if_pos hc] at hField
  change (1 : ℤˣ) • (((cyclicBicomplex k A).d (2 * j + 1) (2 * j)).f r ≫
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) r m) = _
  erw [one_smul, hField] <;> rfl

theorem cyclic_d₂_even (p r m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) (2 * p) (r + 1) m =
      (bComplex k A).d (r + 1) r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r m := by
  erw [(cyclicBicomplex k A).d₂_eq' (ComplexShape.down ℕ) (2 * p)
    (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) m]
  have hp : Even (2 * p) := ⟨p, by omega⟩
  change (ComplexShape.down ℕ).ε (2 * p) •
    (((cyclicBicomplex k A).X (2 * p)).d (r + 1) r ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r m) = _
  erw [ComplexShape.ε_down_ℕ, hp.neg_one_pow, one_smul,
    cyclicBicomplex_vertical, if_pos hp] <;> rfl

theorem cyclic_d₂_odd (j r m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) (2 * j + 1) (r + 1) m =
      -(bPrimeComplex k A).d (r + 1) r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r m := by
  erw [(cyclicBicomplex k A).d₂_eq' (ComplexShape.down ℕ) (2 * j + 1)
    (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) m]
  have hj : Odd (2 * j + 1) := ⟨j, by omega⟩
  have hj' : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  change (ComplexShape.down ℕ).ε (2 * j + 1) •
    (((cyclicBicomplex k A).X (2 * j + 1)).d (r + 1) r ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r m) = _
  erw [ComplexShape.ε_down_ℕ, hj.neg_one_pow, cyclicBicomplex_vertical, if_neg hj']
  simp only [Units.neg_smul, one_smul, neg_comp] <;> rfl

theorem cyclic_d₂_bottom (c m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) c 0 m = 0 :=
  (cyclicBicomplex k A).d₂_eq_zero (ComplexShape.down ℕ) c 0 m
    (by simp [ComplexShape.down_Rel])

theorem cyclicInclusion_d (c r n m : ℕ) (h : c + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r n h ≫
        (cyclicTotal k A).d n m =
      (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) c r m +
        (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) c r m := by
  change (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r n h ≫
    ((cyclicBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
      (cyclicBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

theorem norm_extra_contraction_succ (r : ℕ) :
    (let x : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        (normMap k A (r + 1) ≫ extraDegeneracy k A (r + 1)) ≫
          (bPrimeComplex k A).d (r + 2) (r + 1)
     let y : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        (bComplex k A).d (r + 1) r ≫ normMap k A r ≫ extraDegeneracy k A r
     x + y) = normMap k A (r + 1) := by
  let X₀ := chainLevel k A A r
  let X₁ := chainLevel k A A (r + 1)
  let X₂ := chainLevel k A A (r + 2)
  let N₀ : X₀ ⟶ X₀ := normMap k A r
  let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
  let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
  let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
  let d₀ : X₁ ⟶ X₀ := (bComplex k A).d (r + 1) r
  let d₀' : X₁ ⟶ X₀ := (bPrimeComplex k A).d (r + 1) r
  let d₁' : X₂ ⟶ X₁ := (bPrimeComplex k A).d (r + 2) (r + 1)
  have h := (bPrimeContraction k A).comm (r + 1)
  erw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl),
    prevD_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel (r + 2) (r + 1) from rfl),
    bPrimeContraction_hom, bPrimeContraction_hom] at h
  have hC : 𝟙 X₁ = d₀' ≫ s₀ + s₁ ≫ d₁' := h
  have hSum : s₁ ≫ d₁' + d₀' ≫ s₀ = 𝟙 X₁ :=
    (add_comm (s₁ ≫ d₁') (d₀' ≫ s₀)).trans hC.symm
  have hN : d₀ ≫ N₀ = N₁ ≫ d₀' := (normMap_comp_bPrime_d k A r).symm
  change (N₁ ≫ s₁) ≫ d₁' + d₀ ≫ N₀ ≫ s₀ = N₁
  calc
    _ = N₁ ≫ (s₁ ≫ d₁') + (d₀ ≫ N₀) ≫ s₀ :=
      congrArg₂ (fun f g : X₁ ⟶ X₁ => f + g) (Category.assoc N₁ s₁ d₁')
        (Category.assoc d₀ N₀ s₀).symm
    _ = N₁ ≫ (s₁ ≫ d₁') + (N₁ ≫ d₀') ≫ s₀ :=
      congrArg (fun f : X₁ ⟶ X₀ => N₁ ≫ (s₁ ≫ d₁') + f ≫ s₀) hN
    _ = N₁ ≫ (s₁ ≫ d₁' + d₀' ≫ s₀) :=
      (congrArg (fun f : X₁ ⟶ X₁ => N₁ ≫ (s₁ ≫ d₁') + f)
        (Category.assoc N₁ d₀' s₀)).trans
          (Preadditive.comp_add X₁ X₁ X₁ N₁ (s₁ ≫ d₁') (d₀' ≫ s₀)).symm
    _ = N₁ ≫ 𝟙 X₁ := congrArg (fun f : X₁ ⟶ X₁ => N₁ ≫ f) hSum
    _ = N₁ := Category.comp_id N₁
theorem norm_extra_contraction_bottom :
    (normMap k A 0 ≫ extraDegeneracy k A 0) ≫ (bPrimeComplex k A).d 1 0 =
      normMap k A 0 := by
  let X₀ := chainLevel k A A 0
  let X₁ := chainLevel k A A 1
  let N : X₀ ⟶ X₀ := normMap k A 0
  let s : X₀ ⟶ X₁ := extraDegeneracy k A 0
  let d : X₁ ⟶ X₀ := (bPrimeComplex k A).d 1 0
  have h := (bPrimeContraction k A).comm 0
  erw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq_zero (bPrimeContraction k A).hom 0 (by simp [ComplexShape.down_Rel]),
    prevD_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
    bPrimeContraction_hom, zero_add] at h
  have hC : s ≫ d = 𝟙 X₀ := h.symm
  change (N ≫ s) ≫ d = N
  calc
    _ = N ≫ (s ≫ d) := Category.assoc N s d
    _ = N ≫ 𝟙 X₀ := congrArg (fun f : X₀ ⟶ X₀ => N ≫ f) hC
    _ = N := Category.comp_id N
omit [IsScalarTower k A A] [SMulCommClass k A A] in
theorem boundary_comp_norm_extra (r : ℕ) :
    connesBoundary k A r ≫ normMap k A (r + 1) ≫ extraDegeneracy k A (r + 1) = 0 := by
  let X₀ := chainLevel k A A r
  let X₁ := chainLevel k A A (r + 1)
  let X₂ := chainLevel k A A (r + 2)
  let N₀ : X₀ ⟶ X₀ := normMap k A r
  let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
  let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
  let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
  let t : X₁ ⟶ X₁ := 𝟙 X₁ - cyclicMap k A (r + 1)
  let B : X₀ ⟶ X₁ := connesBoundary k A r
  have hB : B = N₀ ≫ s₀ ≫ t := connesBoundary_eq k A r
  have ht : t ≫ N₁ = 0 := oneSubCyclicMap_comp_normMap k A (r + 1)
  change B ≫ N₁ ≫ s₁ = 0
  calc
    _ = (N₀ ≫ s₀ ≫ t) ≫ N₁ ≫ s₁ :=
      congrArg (fun f : X₀ ⟶ X₁ => f ≫ N₁ ≫ s₁) hB
    _ = N₀ ≫ s₀ ≫ (t ≫ N₁) ≫ s₁ := by simp only [Category.assoc]
    _ = N₀ ≫ s₀ ≫ (0 : X₁ ⟶ X₁) ≫ s₁ :=
      congrArg (fun f : X₁ ⟶ X₁ => N₀ ≫ s₀ ≫ f ≫ s₁) ht
    _ = 0 := by simp only [zero_comp, comp_zero]
theorem mixedCoordinateInclusion_eq (p r q n : ℕ) (h : r + p = q) :
    (ChainComplex.mixedColumnIso (bComplex k A) p r q h).inv ≫
        (connesMixedBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p q n =
      mixedLevelInclusionOrZero k A p r n := by
  subst q
  rfl

theorem mixed_d₁ (p r m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
        (connesMixedBicomplex k A).d₁ (ComplexShape.down ℕ) p (r + p) m =
      if p = 0 then 0 else
        connesBoundary k A r ≫ mixedLevelInclusionOrZero k A (p - 1) (r + 1) m := by
  cases p with
  | zero =>
    erw [if_pos rfl, (connesMixedBicomplex k A).d₁_eq_zero (ComplexShape.down ℕ)
      0 (r + 0) m (by simp [ComplexShape.down_Rel]), comp_zero]
  | succ p =>
    have hField : ((connesMixedBicomplex k A).d (p + 1) p).f (r + (p + 1)) =
        (ChainComplex.mixedColumnIso (bComplex k A) (p + 1) r (r + (p + 1)) rfl).hom ≫
          connesBoundary k A r ≫
            (ChainComplex.mixedColumnIso (bComplex k A) p (r + 1)
              (r + (p + 1)) (by omega)).inv := by
      dsimp only [connesMixedBicomplex, connesMixedConnesDoubleData,
        MixedComplex.ofBoundaryHomotopyConnesDoubleData, ChainComplex.mixedBicomplex]
      erw [ChainComplex.of_d, ChainComplex.mixedHorizontalMap_f,
        ChainComplex.mixedHorizontalComponent_eq _ _ p r (r + (p + 1)) rfl,
        connesBoundaryHomotopy_hom]
    let D := connesMixedBicomplex k A
    let q := r + (p + 1)
    let a : (D.X (p + 1)).X q ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bComplex k A) (p + 1) r q rfl
    let c : (D.X p).X q ≅ chainLevel k A A (r + 1) :=
      ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) q (by dsimp only [q]; omega)
    let i : (D.X p).X q ⟶ (connesMixedTotal k A).X m :=
      D.ιTotalOrZero (ComplexShape.down ℕ) p q m
    let d : (D.X (p + 1)).X q ⟶ (D.X p).X q := (D.d (p + 1) p).f q
    let B : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := connesBoundary k A r
    have hd : d = a.hom ≫ B ≫ c.inv := hField
    have hD : D.d₁ (ComplexShape.down ℕ) (p + 1) q m = (1 : ℤˣ) • (d ≫ i) :=
      D.d₁_eq' (ComplexShape.down ℕ)
        (by rfl : (ComplexShape.down ℕ).Rel (p + 1) p) q m
    have hi : c.inv ≫ i = mixedLevelInclusionOrZero k A p (r + 1) m :=
      mixedCoordinateInclusion_eq k A p (r + 1) q m (by dsimp only [q]; omega)
    erw [if_neg (Nat.succ_ne_zero p)]
    change a.inv ≫ D.d₁ (ComplexShape.down ℕ) (p + 1) q m = B ≫ _
    calc
      _ = a.inv ≫ ((1 : ℤˣ) • (d ≫ i)) :=
        congrArg (fun f : (D.X (p + 1)).X q ⟶ (connesMixedTotal k A).X m => a.inv ≫ f) hD
      _ = a.inv ≫ (d ≫ i) := by rw [one_smul]
      _ = a.inv ≫ ((a.hom ≫ B ≫ c.inv) ≫ i) :=
        congrArg (fun f : (D.X (p + 1)).X q ⟶ (D.X p).X q => a.inv ≫ (f ≫ i)) hd
      _ = B ≫ (c.inv ≫ i) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = B ≫ mixedLevelInclusionOrZero k A p (r + 1) m :=
        congrArg (fun f : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m => B ≫ f) hi

theorem mixed_d₂_succ (p r m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) (r + 1 + p) rfl).inv ≫
        (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p (r + 1 + p) m =
      (bComplex k A).d (r + 1) r ≫ mixedLevelInclusionOrZero k A p r m := by
  let D := connesMixedBicomplex k A
  let a : (D.X p).X (r + 1 + p) ≅ chainLevel k A A (r + 1) :=
    ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) (r + 1 + p) rfl
  let c : (D.X p).X (r + p) ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
  let v : (D.X p).X (r + 1 + p) ⟶ (D.X p).X (r + p) := (D.X p).d (r + 1 + p) (r + p)
  let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := (bComplex k A).d (r + 1) r
  let i : (D.X p).X (r + p) ⟶ (connesMixedTotal k A).X m :=
    D.ιTotalOrZero (ComplexShape.down ℕ) p (r + p) m
  let σ : ℤˣ := (ComplexShape.down ℕ).ε p
  have hD : D.d₂ (ComplexShape.down ℕ) p (r + 1 + p) m = σ • (v ≫ i) :=
    D.d₂_eq' (ComplexShape.down ℕ) p
      (by change r + p + 1 = r + 1 + p; omega) m
  have hv : σ • v = a.hom ≫ d ≫ c.inv := connesMixedTotal_vertical k A p r
  have hi : c.inv ≫ i = mixedLevelInclusionOrZero k A p r m := rfl
  change a.inv ≫ D.d₂ (ComplexShape.down ℕ) p (r + 1 + p) m = d ≫ _
  calc
    _ = a.inv ≫ (σ • (v ≫ i)) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (connesMixedTotal k A).X m => a.inv ≫ f) hD
    _ = a.inv ≫ ((σ • v) ≫ i) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (connesMixedTotal k A).X m => a.inv ≫ f)
        (Linear.units_smul_comp σ v i).symm
    _ = a.inv ≫ ((a.hom ≫ d ≫ c.inv) ≫ i) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (D.X p).X (r + p) => a.inv ≫ (f ≫ i)) hv
    _ = d ≫ (c.inv ≫ i) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = d ≫ mixedLevelInclusionOrZero k A p r m := congrArg (fun f => d ≫ f) hi

theorem mixed_d₂_bottom (p m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p 0 p (Nat.zero_add p)).inv ≫
        (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p p m = 0 := by
  by_cases hp : p = 0
  · subst p
    erw [(connesMixedBicomplex k A).d₂_eq_zero (ComplexShape.down ℕ) 0 0 m
      (by simp [ComplexShape.down_Rel]), comp_zero]
  · erw [(connesMixedBicomplex k A).d₂_eq' (ComplexShape.down ℕ) p
      (show (ComplexShape.down ℕ).Rel p (p - 1) from by
        change p - 1 + 1 = p
        omega) m]
    have hd : ((connesMixedBicomplex k A).X p).d p (p - 1) = 0 :=
      (ChainComplex.mixedColumn_isZero (bComplex k A) p (p - 1) (by omega)).eq_of_tgt _ _
    erw [hd, zero_comp, smul_zero, comp_zero]

theorem mixedInclusion_d_succ (p r n m : ℕ) (h : 2 * p + (r + 1) = n) :
    mixedLevelInclusion k A p (r + 1) n h ≫ (connesMixedTotal k A).d n m =
      (let x : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m :=
          if p = 0 then 0 else
            connesBoundary k A (r + 1) ≫ mixedLevelInclusionOrZero k A (p - 1) (r + 2) m
       let y : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m :=
          (bComplex k A).d (r + 1) r ≫ mixedLevelInclusionOrZero k A p r m
       x + y) := by
  unfold mixedLevelInclusion
  change (_ ≫ _) ≫ ((connesMixedBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
    (connesMixedBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, Category.assoc, Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, mixed_d₁, mixed_d₂_succ]

theorem mixedInclusion_d_bottom (p n m : ℕ) (h : 2 * p + 0 = n) :
    mixedLevelInclusion k A p 0 n h ≫ (connesMixedTotal k A).d n m =
      if p = 0 then 0 else connesBoundary k A 0 ≫
        mixedLevelInclusionOrZero k A (p - 1) 1 m := by
  unfold mixedLevelInclusion
  change (_ ≫ _) ≫ ((connesMixedBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
    (connesMixedBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, Category.assoc, Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, mixed_d₁]
  let x : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m :=
    if p = 0 then 0 else connesBoundary k A 0 ≫ mixedLevelInclusionOrZero k A (p - 1) 1 m
  let z : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m :=
    (ChainComplex.mixedColumnIso (bComplex k A) p 0 (0 + p) rfl).inv ≫
      (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p (0 + p) m
  have hz : z = 0 := by
    have hbottom : ∀ (q : ℕ) (hq : 0 + p = q),
        (ChainComplex.mixedColumnIso (bComplex k A) p 0 q hq).inv ≫
          (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p q m = 0 := by
      intro q hq
      have hqp : q = p := hq.symm.trans (Nat.zero_add p)
      cases hqp
      exact mixed_d₂_bottom k A p m
    exact hbottom (0 + p) rfl
  change x + z = x
  exact (congrArg (fun a : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m => x + a) hz).trans
    (add_zero x)

theorem connesOddInclusion_dOrZero (j r n m : ℕ)
    (h : (r + 1) + (2 * j + 1) = n) :
    connesOddInclusion k A j (r + 1) n h ≫ (connesOddTotal k A).d n m =
      -(bPrimeComplex k A).d (r + 1) r ≫ connesOddInclusionOrZero k A j r m := by
  by_cases hm : r + (2 * j + 1) = m
  · erw [connesOddInclusionOrZero_eq k A j r m hm, connesOddInclusion_d]
  · have hnm : ¬ (ComplexShape.down ℕ).Rel n m := by
      change m + 1 ≠ n
      omega
    erw [(connesOddTotal k A).shape n m hnm, comp_zero, connesOddInclusionOrZero,
      dif_neg hm, comp_zero]
    exact neg_zero.symm

theorem connesOddInclusion_d_bottom (j n m : ℕ) (h : 0 + (2 * j + 1) = n) :
    connesOddInclusion k A j 0 n h ≫ (connesOddTotal k A).d n m = 0 := by
  let P := connesOddFamily k A
  let X : ℕ → ModuleCat.{max u v} k := P.X n
  let Y : ℕ → ModuleCat.{max u v} k := P.X m
  let f : ∀ a : ℕ, X a ⟶ Y a := P.d n m
  let a : chainLevel k A A 0 ⟶ X j :=
    (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) 0 n h).inv
  let i : X j ⟶ (connesOddTotal k A).X n := Sigma.ι X j
  let i' : Y j ⟶ (connesOddTotal k A).X m := Sigma.ι Y j
  let t : (connesOddTotal k A).X n ⟶ (connesOddTotal k A).X m :=
    CategoryTheory.Limits.Sigma.map f
  have hi : i ≫ t = f j ≫ i' := CategoryTheory.Limits.Sigma.ι_map f j
  let K := bPrimeComplex k A
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) (2 * j + 1)
  let L : ChainComplex (ModuleCat.{max u v} k) ℕ := K.extend E
  let d : L.X n ⟶ L.X m := L.d n m
  let σ : ℤˣ := (-1 : ℤˣ) ^ (2 * j + 1)
  have hd : d = 0 := K.extend_d_from_eq_zero E n m 0 h
    (by simp [ComplexShape.down_Rel])
  have hv : f j = σ • d := rfl
  have hf : f j = 0 := hv.trans
    ((congrArg (fun g : L.X n ⟶ L.X m => σ • g) hd).trans (smul_zero σ))
  have ht : i ≫ t = 0 := hi.trans
    ((congrArg (fun g : X j ⟶ Y j => g ≫ i') hf).trans zero_comp)
  have hall : (a ≫ i) ≫ t = 0 := (Category.assoc a i t).trans
    ((congrArg (fun g : X j ⟶ (connesOddTotal k A).X m => a ≫ g) ht).trans comp_zero)
  change (a ≫ i) ≫ t = 0
  exact hall

theorem boundary_comp_levelImage (p r n : ℕ) :
    connesBoundary k A r ≫ mixedToCyclicLevelImage k A p (r + 1) n =
      connesBoundary k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 1) n := by
  let B : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := connesBoundary k A r
  let N : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) := normMap k A (r + 1)
  let S : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := extraDegeneracy k A (r + 1)
  let i₀ : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 1) n
  let i₁ : chainLevel k A A (r + 2) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 2) n
  let c : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
    if p = 0 then 0 else N ≫ S ≫ i₁
  have hImage : mixedToCyclicLevelImage k A p (r + 1) n = i₀ + c := rfl
  have hB : B ≫ N ≫ S = 0 := boundary_comp_norm_extra k A r
  have hz : B ≫ (N ≫ S ≫ i₁) = 0 := by
    calc
      _ = B ≫ ((N ≫ S) ≫ i₁) :=
        congrArg (fun a : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n => B ≫ a)
          (Category.assoc N S i₁).symm
      _ = (B ≫ (N ≫ S)) ≫ i₁ := (Category.assoc B (N ≫ S) i₁).symm
      _ = 0 ≫ i₁ :=
        congrArg (fun a : chainLevel k A A r ⟶ chainLevel k A A (r + 2) => a ≫ i₁) hB
      _ = 0 := zero_comp
  have hc : B ≫ c = 0 := by
    by_cases hp : p = 0
    · dsimp only [c]
      rw [if_pos hp, comp_zero]
    · dsimp only [c]
      rw [if_neg hp]
      exact hz
  change B ≫ mixedToCyclicLevelImage k A p (r + 1) n = B ≫ i₀
  calc
    _ = B ≫ (i₀ + c) :=
      congrArg (fun a : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n => B ≫ a) hImage
    _ = B ≫ i₀ + B ≫ c :=
      Preadditive.comp_add (chainLevel k A A r) (chainLevel k A A (r + 1))
        ((cyclicTotal k A).X n) B i₀ c
    _ = B ≫ i₀ + 0 :=
      congrArg (fun a : chainLevel k A A r ⟶ (cyclicTotal k A).X n => B ≫ i₀ + a) hc
    _ = B ≫ i₀ := add_zero _

theorem oneSub_comp_evenImage (p r n : ℕ) :
    (𝟙 (chainLevel k A A r) - cyclicMap k A r) ≫ cyclicToOddEvenImage k A p r n = 0 := by
  unfold cyclicToOddEvenImage
  by_cases hp : p = 0
  · erw [if_pos hp, comp_zero]
  · erw [if_neg hp, comp_neg]
    have hz := congrArg (fun a => a ≫ extraDegeneracy k A r ≫
      connesOddInclusionOrZero k A (p - 1) (r + 1) n)
      (oneSubCyclicMap_comp_normMap k A r)
    simpa only [Category.assoc, zero_comp, neg_zero] using congrArg Neg.neg hz

theorem mixedToCyclicComponent_cell_comm (p r n : ℕ) (h : 2 * p + r = n + 1) :
    (mixedLevelInclusion k A p r (n + 1) h ≫ mixedToCyclicComponent k A (n + 1)) ≫
        (cyclicTotal k A).d (n + 1) n =
      (mixedLevelInclusion k A p r (n + 1) h ≫ (connesMixedTotal k A).d (n + 1) n) ≫
        mixedToCyclicComponent k A n := by
  erw [mixedToCyclicComponent_levelImage]
  cases p with
  | zero =>
    cases r with
    | zero => omega
    | succ r =>
      erw [mixedToCyclicLevelImage, if_pos rfl, add_zero,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 (r + 1)
          (n + 1) (by change 0 + (r + 1) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even k A 0 (r + 1) n, if_pos rfl,
        cyclic_d₂_even k A 0 r n, zero_add,
        mixedInclusion_d_succ k A 0 r (n + 1) n h, if_pos rfl, zero_add,
        Category.assoc, mixedToCyclicComponent_inclusionOrZero]
      simp only [mixedToCyclicLevelImage, if_pos rfl, if_true, add_zero]
      erw [_root_.add_zero]
  | succ p =>
    have hc : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    cases r with
    | zero =>
      erw [mixedToCyclicLevelImage, if_neg (Nat.succ_ne_zero p), hc, add_comp,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) 0
          (n + 1) (by change 2 * (p + 1) + 0 = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even,
        if_neg (Nat.succ_ne_zero p), cyclic_d₂_bottom, add_zero, hc,
        Category.assoc, Category.assoc,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p + 1) 1
          (n + 1) (by change (2 * p + 1) + 1 = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd,
        mixedInclusion_d_bottom k A (p + 1) (n + 1) n h,
        if_neg (Nat.succ_ne_zero p), Nat.add_sub_cancel]
      conv_rhs => repeat erw [Category.assoc]
      erw [mixedToCyclicComponent_inclusionOrZero k A p 1 n,
        boundary_comp_levelImage k A p 0 n]
      let N : chainLevel k A A 0 ⟶ chainLevel k A A 0 := normMap k A 0
      let S : chainLevel k A A 0 ⟶ chainLevel k A A 1 := extraDegeneracy k A 0
      let d : chainLevel k A A 1 ⟶ chainLevel k A A 0 := (bPrimeComplex k A).d 1 0
      let T : chainLevel k A A 1 ⟶ chainLevel k A A 1 := cyclicMap k A 1
      let B : chainLevel k A A 0 ⟶ chainLevel k A A 1 := connesBoundary k A 0
      let io : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) 0 n
      let ie : chainLevel k A A 1 ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) 1 n
      have hCancel : (N ≫ S) ≫ d = N := norm_extra_contraction_bottom k A
      have hBoundary : (N ≫ S) ≫ (𝟙 (chainLevel k A A 1) - T) = B :=
        (Category.assoc N S _).trans (connesBoundary_eq k A 0).symm
      have ho : (N ≫ S) ≫ (d ≫ io) = N ≫ io :=
        (Category.assoc (N ≫ S) d io).symm.trans
          (congrArg (fun f : chainLevel k A A 0 ⟶ chainLevel k A A 0 => f ≫ io) hCancel)
      have he : (N ≫ S) ≫ ((𝟙 (chainLevel k A A 1) - T) ≫ ie) = B ≫ ie :=
        (Category.assoc (N ≫ S) _ ie).symm.trans
          (congrArg (fun f : chainLevel k A A 0 ⟶ chainLevel k A A 1 => f ≫ ie) hBoundary)
      change N ≫ io + (N ≫ S) ≫
        ((𝟙 (chainLevel k A A 1) - T) ≫ ie + -(d ≫ io)) = B ≫ ie
      calc
        _ = N ≫ io + (N ≫ S) ≫ ((𝟙 (chainLevel k A A 1) - T) ≫ ie) -
            (N ≫ S) ≫ (d ≫ io) := by
          erw [comp_add, comp_neg]
          simp only [sub_eq_add_neg, Preadditive.neg_comp, Category.assoc]
          abel
        _ = N ≫ io + B ≫ ie - N ≫ io :=
          congrArg₂ (fun f g : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n => N ≫ io + f - g) he ho
        _ = B ≫ ie := by abel
    | succ r =>
      erw [mixedToCyclicLevelImage, if_neg (Nat.succ_ne_zero p), hc, add_comp,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) (r + 1)
          (n + 1) (by change 2 * (p + 1) + (r + 1) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even,
        if_neg (Nat.succ_ne_zero p), cyclic_d₂_even, hc,
        Category.assoc, Category.assoc,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p + 1) (r + 2)
          (n + 1) (by change (2 * p + 1) + (r + 2) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd,
        mixedInclusion_d_succ k A (p + 1) r (n + 1) n h,
        if_neg (Nat.succ_ne_zero p), Nat.add_sub_cancel,
        add_comp, Category.assoc, Category.assoc]
      conv_rhs => repeat erw [Category.assoc]
      erw [mixedToCyclicComponent_inclusionOrZero k A p (r + 2) n,
        mixedToCyclicComponent_inclusionOrZero k A (p + 1) r n,
        boundary_comp_levelImage k A p (r + 1) n]
      let N : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) := normMap k A (r + 1)
      let S : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := extraDegeneracy k A (r + 1)
      let d : chainLevel k A A (r + 2) ⟶ chainLevel k A A (r + 1) :=
        (bPrimeComplex k A).d (r + 2) (r + 1)
      let d₀ : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := (bComplex k A).d (r + 1) r
      let N₀ : chainLevel k A A r ⟶ chainLevel k A A r := normMap k A r
      let S₀ : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := extraDegeneracy k A r
      let T : chainLevel k A A (r + 2) ⟶ chainLevel k A A (r + 2) := cyclicMap k A (r + 2)
      let B : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := connesBoundary k A (r + 1)
      let io : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) (r + 1) n
      let ie : chainLevel k A A (r + 2) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 2) n
      let i₀ : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * (p + 1)) r n
      have hImage : mixedToCyclicLevelImage k A (p + 1) r n = i₀ + N₀ ≫ S₀ ≫ io := by
        dsimp only [mixedToCyclicLevelImage]
        erw [if_neg (Nat.succ_ne_zero p), hc] <;> rfl
      have hCancel : (N ≫ S) ≫ d + d₀ ≫ N₀ ≫ S₀ = N := norm_extra_contraction_succ k A r
      have hBoundary : (N ≫ S) ≫ (𝟙 (chainLevel k A A (r + 2)) - T) = B :=
        (Category.assoc N S _).trans (connesBoundary_eq k A (r + 1)).symm
      have ho : N ≫ io = ((N ≫ S) ≫ d) ≫ io + (d₀ ≫ N₀ ≫ S₀) ≫ io := by
        have h := congrArg
          (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) => f ≫ io) hCancel
        rw [add_comp] at h
        exact h.symm
      have he : (N ≫ S) ≫ ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie) = B ≫ ie :=
        (Category.assoc (N ≫ S) _ ie).symm.trans
          (congrArg (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) => f ≫ ie) hBoundary)
      erw [hImage]
      change N ≫ io + d₀ ≫ i₀ + (N ≫ S) ≫
        ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie + -(d ≫ io)) =
          B ≫ ie + d₀ ≫ (i₀ + N₀ ≫ S₀ ≫ io)
      calc
        _ = N ≫ io + d₀ ≫ i₀ + (N ≫ S) ≫
            ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie) - (N ≫ S) ≫ (d ≫ io) := by
          erw [comp_add, comp_neg]
          simp only [sub_eq_add_neg, Preadditive.neg_comp, Category.assoc]
          abel
        _ = N ≫ io + d₀ ≫ i₀ + B ≫ ie - ((N ≫ S) ≫ d) ≫ io :=
          congrArg₂ (fun f g : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n =>
            N ≫ io + d₀ ≫ i₀ + f - g) he (Category.assoc (N ≫ S) d io).symm
        _ = B ≫ ie + d₀ ≫ i₀ + (d₀ ≫ N₀ ≫ S₀) ≫ io := by
          rw [ho]
          abel
        _ = B ≫ ie + d₀ ≫ (i₀ + N₀ ≫ S₀ ≫ io) := by
          erw [comp_add]
          simp only [Category.assoc]
          abel

theorem mixedToCyclicComponent_comm (n : ℕ) :
    mixedToCyclicComponent k A (n + 1) ≫ (cyclicTotal k A).d (n + 1) n =
      (connesMixedTotal k A).d (n + 1) n ≫ mixedToCyclicComponent k A n := by
  apply connesMixedTotal_hom_ext k A (n + 1)
  intro p r h
  simpa only [Category.assoc] using mixedToCyclicComponent_cell_comm k A p r n h

/-- The positive printed inclusion is a chain map, with no supplied compatibility. -/
def mixedToCyclic : connesMixedTotal k A ⟶ cyclicTotal k A :=
  ChainComplex.ofHom (mixedToCyclicComponent k A) (mixedToCyclicComponent_comm k A)

/-- The chain map retains its computed positive total-degree component. -/
@[simp]
theorem mixedToCyclic_f (n : ℕ) : (mixedToCyclic k A).f n = mixedToCyclicComponent k A n := rfl

/-- The original first column has no negative-column correction. -/
theorem mixedToCyclic_ι_zero (r : ℕ) :
    mixedLevelInclusion k A 0 r r (by omega) ≫ (mixedToCyclic k A).f r =
      (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 r r (by change 0 + r = r; omega) := by
  erw [mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  dsimp only [mixedToCyclicLevelImage]
  erw [if_pos rfl, add_zero]
  exact (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 r r
    (by change 0 + r = r; omega)

/-- Every later column has exactly the original positive sN correction. -/
theorem mixedToCyclic_ι_succ (p r n : ℕ) (h : 2 * (p + 1) + r = n) :
    mixedLevelInclusion k A (p + 1) r n h ≫ (mixedToCyclic k A).f n =
      (let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * (p + 1)) r n h
       let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          normMap k A r ≫ extraDegeneracy k A r ≫
            (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p + 1) (r + 1) n
              (by change (2 * p + 1) + (r + 1) = n; omega)
       x + y) := by
  erw [mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  unfold mixedToCyclicLevelImage
  erw [if_neg (Nat.succ_ne_zero p),
    (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) r n h]
  have hc : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
  erw [hc, (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ)
    (2 * p + 1) (r + 1) n (by change (2 * p + 1) + (r + 1) = n; omega)]

theorem cyclicToOddComponent_cell_comm (c r n : ℕ) (h : c + r = n + 1) :
    ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r (n + 1) h ≫
        cyclicToOddComponent k A (n + 1)) ≫ (connesOddTotal k A).d (n + 1) n =
      ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r (n + 1) h ≫
        (cyclicTotal k A).d (n + 1) n) ≫ cyclicToOddComponent k A n := by
  by_cases hc : Even c
  · obtain ⟨p, hp⟩ := hc
    have hcp : c = 2 * p := by omega
    clear hp
    subst c
    cases p with
    | zero =>
      cases r with
      | zero => omega
      | succ r =>
        have hZero : connesOddInclusionOrZero k A (0 - 1) (r + 2) (n + 1) = 0 := by
          unfold connesOddInclusionOrZero
          exact dif_neg (by omega)
        erw [cyclicToOddComponent_even k A 0 (r + 1) (n + 1) h,
          hZero, comp_zero, neg_zero, zero_comp]
        erw [cyclicInclusion_d, cyclic_d₁_even, if_pos rfl, cyclic_d₂_even, zero_add,
          Category.assoc, cyclicToOddComponent_evenOrZero]
        simp only [cyclicToOddEvenImage, if_pos rfl, if_true, comp_zero]
        erw [comp_zero]
    | succ p =>
      have hcol : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
      erw [cyclicToOddComponent_even]
      cases r with
      | zero =>
        erw [connesOddInclusionOrZero_eq k A p 1 (n + 1) (by omega), neg_comp,
          Category.assoc, Category.assoc, connesOddInclusion_dOrZero,
          cyclicInclusion_d, cyclic_d₁_even, if_neg (Nat.succ_ne_zero p),
          cyclic_d₂_bottom, add_zero, hcol]
        let N : chainLevel k A A 0 ⟶ chainLevel k A A 0 := normMap k A 0
        let s : chainLevel k A A 0 ⟶ chainLevel k A A 1 := extraDegeneracy k A 0
        let d : chainLevel k A A 1 ⟶ chainLevel k A A 0 := (bPrimeComplex k A).d 1 0
        let io : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) 0 n
        let iq : chainLevel k A A 0 ⟶ (connesOddTotal k A).X n :=
          connesOddInclusionOrZero k A p 0 n
        let q : (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
          cyclicToOddComponent k A n
        have ho : io ≫ q = iq := cyclicToOddComponent_oddOrZero k A p 0 n
        have hCancel : ((N ≫ s) ≫ d) ≫ iq = N ≫ iq :=
          congrArg (fun a : chainLevel k A A 0 ⟶ chainLevel k A A 0 => a ≫ iq)
            (norm_extra_contraction_bottom k A)
        change @Eq (chainLevel k A A 0 ⟶ (connesOddTotal k A).X n)
          (-(N ≫ s ≫ (-(d ≫ iq)))) ((N ≫ io) ≫ q)
        erw [Category.assoc N io q, ho]
        simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
        simpa only [Category.assoc] using hCancel
      | succ r =>
        erw [connesOddInclusionOrZero_eq k A p (r + 2) (n + 1) (by omega), neg_comp,
          Category.assoc, Category.assoc, connesOddInclusion_dOrZero,
          cyclicInclusion_d, cyclic_d₁_even, if_neg (Nat.succ_ne_zero p),
          cyclic_d₂_even, hcol,
          add_comp, Category.assoc, Category.assoc,
          cyclicToOddComponent_oddOrZero, cyclicToOddComponent_evenOrZero]
        let X₀ := chainLevel k A A r
        let X₁ := chainLevel k A A (r + 1)
        let X₂ := chainLevel k A A (r + 2)
        let N₀ : X₀ ⟶ X₀ := normMap k A r
        let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
        let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
        let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
        let d₀ : X₁ ⟶ X₀ := (bComplex k A).d (r + 1) r
        let d₁' : X₂ ⟶ X₁ := (bPrimeComplex k A).d (r + 2) (r + 1)
        let iq : X₁ ⟶ (connesOddTotal k A).X n :=
          connesOddInclusionOrZero k A p (r + 1) n
        change @Eq (X₁ ⟶ (connesOddTotal k A).X n)
          (-(N₁ ≫ s₁ ≫ (-(d₁' ≫ iq))))
          (N₁ ≫ iq + d₀ ≫ (-(N₀ ≫ s₀ ≫ iq)))
        have hContraction : (N₁ ≫ s₁) ≫ d₁' + d₀ ≫ N₀ ≫ s₀ = N₁ :=
          norm_extra_contraction_succ k A r
        have hCancel := congrArg (fun x : X₁ ⟶ X₁ => x ≫ iq) hContraction
        rw [Preadditive.add_comp] at hCancel
        simp only [Category.assoc] at hCancel
        simp only [neg_one_zsmul, Units.neg_smul, one_smul,
          Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
        erw [← hCancel]
        abel
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hc
    have hcj : c = 2 * j + 1 := by omega
    clear hj
    subst c
    erw [cyclicToOddComponent_odd]
    cases r with
    | zero =>
      erw [connesOddInclusion_d_bottom k A j (n + 1) n (by omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_bottom, add_zero,
        Category.assoc, cyclicToOddComponent_evenOrZero, oneSub_comp_evenImage]
    | succ r =>
      erw [connesOddInclusion_dOrZero,
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd, add_comp]
      let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r :=
        (bPrimeComplex k A).d (r + 1) r
      let a : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        𝟙 (chainLevel k A A (r + 1)) - cyclicMap k A (r + 1)
      let ie : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) (r + 1) n
      let io : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n
      let iq : chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
        connesOddInclusionOrZero k A j r n
      let q : (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
        cyclicToOddComponent k A n
      have hEven : ie ≫ q = cyclicToOddEvenImage k A j (r + 1) n :=
        cyclicToOddComponent_evenOrZero k A j (r + 1) n
      have hOdd : io ≫ q = iq := cyclicToOddComponent_oddOrZero k A j r n
      have he : (a ≫ ie) ≫ q = 0 :=
        (Category.assoc a ie q).trans
          ((congrArg (fun x : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n =>
            a ≫ x) hEven).trans (oneSub_comp_evenImage k A j (r + 1) n))
      have ho : (-(d ≫ io)) ≫ q = -(d ≫ iq) := by
        rw [Preadditive.neg_comp, Category.assoc d io q, hOdd]
      change @Eq (chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n)
        (-(d ≫ iq)) (((a ≫ ie) ≫ q) + ((-(d ≫ io)) ≫ q))
      exact ((congrArg₂ (fun x y : chainLevel k A A (r + 1) ⟶
          (connesOddTotal k A).X n => x + y) he ho).trans (zero_add (-(d ≫ iq)))).symm

theorem cyclicToOddComponent_comm (n : ℕ) :
    cyclicToOddComponent k A (n + 1) ≫ (connesOddTotal k A).d (n + 1) n =
      (cyclicTotal k A).d (n + 1) n ≫ cyclicToOddComponent k A n := by
  apply HomologicalComplex₂.total.hom_ext
  intro c r h
  simpa only [Category.assoc] using cyclicToOddComponent_cell_comm k A c r n h

/-- The computed (-sN,id) quotient is a chain map to the contractible odd columns. -/
def cyclicToOdd : cyclicTotal k A ⟶ connesOddTotal k A :=
  ChainComplex.ofHom (cyclicToOddComponent k A) (cyclicToOddComponent_comm k A)

/-- The quotient map retains its computed original even/odd components. -/
@[simp]
theorem cyclicToOdd_f (n : ℕ) : (cyclicToOdd k A).f n = cyclicToOddComponent k A n := rfl

theorem mixedEvenProjection_evenOrZero (p r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n ≫
        mixedEvenProjection k A n = mixedLevelInclusionOrZero k A p r n := by
  by_cases h : 2 * p + r = n
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p) r n h,
      mixedEvenProjection_even k A p r n h, mixedLevelInclusionOrZero_eq k A p r n h]
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ) (2 * p) r n h,
      zero_comp]
    unfold mixedLevelInclusionOrZero
    erw [(connesMixedBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p (r + p) n
      (by change p + (r + p) ≠ n; omega), comp_zero] <;> rfl

theorem mixedEvenProjection_oddOrZero (j r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n ≫
        mixedEvenProjection k A n = 0 := by
  by_cases h : 2 * j + 1 + r = n
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * j + 1) r n h,
      mixedEvenProjection_odd k A j r n h]
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ)
      (2 * j + 1) r n h, zero_comp]

theorem mixedToCyclic_evenProjection (n : ℕ) :
    (mixedToCyclic k A).f n ≫ mixedEvenProjection k A n = 𝟙 _ := by
  apply connesMixedTotal_hom_ext k A n
  intro p r h
  erw [← Category.assoc, mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  unfold mixedToCyclicLevelImage
  erw [add_comp, mixedEvenProjection_evenOrZero, mixedLevelInclusionOrZero_eq k A p r n h]
  by_cases hp : p = 0
  · erw [if_pos hp, zero_comp, add_zero, Category.comp_id]
  · let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let C := (cyclicTotal k A).X n
    let M := (connesMixedTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    let i : Y ⟶ C :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    let P : C ⟶ M := mixedEvenProjection k A n
    let x : X ⟶ M := mixedLevelInclusion k A p r n h
    have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
    have hi : i ≫ P = 0 := by
      change (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n ≫ mixedEvenProjection k A n = 0
      erw [hcol]
      exact mixedEvenProjection_oddOrZero k A (p - 1) (r + 1) n
    have hy : (N ≫ S ≫ i) ≫ P = 0 := by
      calc
        _ = (N ≫ S) ≫ (i ≫ P) := by simp only [Category.assoc]
        _ = (N ≫ S) ≫ (0 : Y ⟶ M) :=
          congrArg (fun f : Y ⟶ M => (N ≫ S) ≫ f) hi
        _ = 0 := comp_zero
    erw [if_neg hp]
    change x + (N ≫ S ≫ i) ≫ P = x
    exact (congrArg (fun f : X ⟶ M => x + f) hy).trans (add_zero x)
theorem oddSection_cyclicToOdd (n : ℕ) :
    connesOddSection k A n ≫ (cyclicToOdd k A).f n = 𝟙 _ := by
  apply connesOddTotal_hom_ext k A n
  intro j r h
  erw [← Category.assoc, connesOddInclusion_section, cyclicToOdd_f,
    cyclicToOddComponent_oddOrZero, connesOddInclusionOrZero_eq k A j r n h,
    Category.comp_id]

theorem mixedToCyclic_comp_cyclicToOdd : mixedToCyclic k A ≫ cyclicToOdd k A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (mixedToCyclic k A).f n ≫ (cyclicToOdd k A).f n = 0
  apply connesMixedTotal_hom_ext k A n
  intro p r h
  erw [← Category.assoc, mixedToCyclic_f, mixedToCyclicComponent_levelImage, cyclicToOdd_f]
  unfold mixedToCyclicLevelImage
  erw [add_comp, cyclicToOddComponent_evenOrZero]
  by_cases hp : p = 0
  · simp only [if_pos hp, cyclicToOddEvenImage, zero_comp, add_zero, comp_zero]
  · let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let C := (cyclicTotal k A).X n
    let O := (connesOddTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    let i : Y ⟶ C :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    let j : Y ⟶ O := connesOddInclusionOrZero k A (p - 1) (r + 1) n
    let Q : C ⟶ O := cyclicToOddComponent k A n
    let F : X ⟶ O := N ≫ S ≫ j
    have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
    have hi : i ≫ Q = j := by
      change (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n ≫ cyclicToOddComponent k A n = j
      erw [hcol]
      exact cyclicToOddComponent_oddOrZero k A (p - 1) (r + 1) n
    have hy : (N ≫ S ≫ i) ≫ Q = F := by
      calc
        _ = (N ≫ S) ≫ (i ≫ Q) := by simp only [Category.assoc]
        _ = (N ≫ S) ≫ j := congrArg (fun f : Y ⟶ O => (N ≫ S) ≫ f) hi
        _ = F := Category.assoc N S j
    have hEven : cyclicToOddEvenImage k A p r n = -F := if_neg hp
    erw [if_neg hp]
    change cyclicToOddEvenImage k A p r n + (N ≫ S ≫ i) ≫ Q = 0
    exact (congrArg₂ (fun f g : X ⟶ O => f + g) hEven hy).trans (neg_add_cancel F)
theorem mixedCyclicSplitting_id (n : ℕ) :
    mixedEvenProjection k A n ≫ (mixedToCyclic k A).f n +
        (cyclicToOdd k A).f n ≫ connesOddSection k A n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro c r h
  change c + r = n at h
  erw [comp_add, ← Category.assoc, ← Category.assoc, cyclicToOdd_f]
  by_cases hc : Even c
  · obtain ⟨p, hp⟩ := hc
    have hcp : c = 2 * p := by omega
    clear hp
    subst c
    erw [mixedEvenProjection_even, mixedToCyclic_f, mixedToCyclicComponent_levelImage,
      cyclicToOddComponent_even]
    unfold mixedToCyclicLevelImage
    by_cases hp : p = 0
    · subst p
      have hz : connesOddInclusionOrZero k A (0 - 1) (r + 1) n = 0 := by
        unfold connesOddInclusionOrZero
        erw [dif_neg (by omega)]
      erw [if_pos rfl, hz, comp_zero, neg_zero, zero_comp, add_zero, add_zero]
      simpa only [Category.comp_id] using
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 r n h
    · let X := chainLevel k A A r
      let Y := chainLevel k A A (r + 1)
      let C := (cyclicTotal k A).X n
      let O := (connesOddTotal k A).X n
      let N : X ⟶ X := normMap k A r
      let S : X ⟶ Y := extraDegeneracy k A r
      let i₀ : X ⟶ C :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
      let i : Y ⟶ C :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
      let j : Y ⟶ O := connesOddInclusionOrZero k A (p - 1) (r + 1) n
      let Q : O ⟶ C := connesOddSection k A n
      let F : X ⟶ O := N ≫ S ≫ j
      let V : X ⟶ C := N ≫ S ≫ i
      have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
      have hj : j ≫ Q = i := by
        change connesOddInclusionOrZero k A (p - 1) (r + 1) n ≫ connesOddSection k A n =
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
        erw [hcol]
        exact connesOddInclusionOrZero_section k A (p - 1) (r + 1) n
      have hF : F ≫ Q = V := by
        calc
          _ = (N ≫ S) ≫ (j ≫ Q) := by simp only [F, Category.assoc]
          _ = (N ≫ S) ≫ i := congrArg (fun f : Y ⟶ C => (N ≫ S) ≫ f) hj
          _ = V := Category.assoc N S i
      have hNeg : (-F) ≫ Q = -V :=
        (Preadditive.neg_comp F Q).trans (congrArg (fun f : X ⟶ C => -f) hF)
      have hi₀ : i₀ = (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h :=
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p) r n h
      erw [if_neg hp]
      change (i₀ + V) + (-F) ≫ Q =
        (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫ 𝟙 C
      have hAdd : (i₀ + V) + -V = i₀ := _root_.add_neg_cancel_right i₀ V
      have hId : (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫ 𝟙 C =
          (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h :=
        Category.comp_id _
      exact (congrArg (fun f : X ⟶ C => (i₀ + V) + f) hNeg).trans
        (hAdd.trans (hi₀.trans hId.symm))
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hc
    have hcj : c = 2 * j + 1 := by omega
    clear hj
    subst c
    erw [mixedEvenProjection_odd, zero_comp, cyclicToOddComponent_odd,
      connesOddInclusion_section, zero_add,
      (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * j + 1) r n h,
      Category.comp_id]

/-- The printed inclusion and computed odd quotient form the native short complex. -/
def mixedCyclicShortComplex : ShortComplex (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  ShortComplex.mk (mixedToCyclic k A) (cyclicToOdd k A)
    (mixedToCyclic_comp_cyclicToOdd k A)

/-- The original even projection and odd insertion earn the degreewise splitting. -/
def mixedCyclicSplitting (n : ℕ) :
    ((mixedCyclicShortComplex k A).map
      (HomologicalComplex.eval _ (ComplexShape.down ℕ) n)).Splitting where
  r := mixedEvenProjection k A n
  s := connesOddSection k A n
  f_r := mixedToCyclic_evenProjection k A n
  s_g := oddSection_cyclicToOdd k A n
  id := mixedCyclicSplitting_id k A n

/-- Native degreewise-split cancellation earns the equivalence with the positive I. -/
def mixedToCyclicHomotopyEquiv : HomotopyEquiv (connesMixedTotal k A) (cyclicTotal k A) :=
  ChainComplex.homotopyEquivOfDegreewiseSplit (mixedCyclicShortComplex k A)
    (mixedCyclicSplitting k A) (connesOddContraction k A)

/-- The equivalence's forward map is the original positive printed inclusion. -/
@[simp]
theorem mixedToCyclicHomotopyEquiv_hom :
    (mixedToCyclicHomotopyEquiv k A).hom = mixedToCyclic k A :=
  ChainComplex.homotopyEquivOfDegreewiseSplit_hom _ _ _

/-- The positive printed inclusion is a quasi-isomorphism, without a supplied certificate. -/
theorem mixedToCyclic_quasiIso : QuasiIso (mixedToCyclic k A) := by
  simpa only [mixedToCyclicHomotopyEquiv_hom] using
    (mixedToCyclicHomotopyEquiv k A).quasiIso_hom

/-- The mixed total has the already constructed cyclic homology. -/
def mixedCyclicHomologyIso (n : ℕ) :
    (connesMixedTotal k A).homology n ≅ cyclicHomology k A n :=
  (mixedToCyclicHomotopyEquiv k A).toHomologyIso n

/-- The homology comparison is induced by the positive printed map. -/
@[simp]
theorem mixedCyclicHomologyIso_hom (n : ℕ) :
    (mixedCyclicHomologyIso k A n).hom = homologyMap (mixedToCyclic k A) n := by
  change homologyMap (mixedToCyclicHomotopyEquiv k A).hom n = _
  rw [mixedToCyclicHomotopyEquiv_hom]

/-- Native lifting commutes with the finite diagonal total of the raw mixed model. -/
def connesMixedTotalLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedTotal k A) ≅
        ((HomologicalComplex₂.total
            ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (connesMixedBicomplex k A))) (ComplexShape.down ℕ)) := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let R := connesMixedBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  exact HomologicalComplex₂.functorTotalIso U R

/-- Exact lifting and the native finite-diagonal comparison identify the raw mixed homology. -/
def connesMixedHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj ((connesMixedTotal k A).homology n) ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).homology n := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let h : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k A)).homology n ≅ U.obj ((connesMixedTotal k A).homology n) :=
    ((connesMixedTotal k A).sc n).mapHomologyIso U
  exact h.symm ≪≫ HomologicalComplex.homologyMapIso (connesMixedTotalLiftIso.{lift} k A) n

/-- Lifted supported coordinates still include the original bar level in the native mixed total. -/
def mixedLevelInclusionLift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (p r n : ℕ) (h : 2 * p + r = n) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj (chainLevel k A A r) ⟶
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).X n :=
  (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map
      (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (HomologicalComplex₂.ιTotal
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)

/-- The original supported inclusion has exactly its computed lifted-column coordinates. -/
@[reassoc]
theorem map_mixedLevelInclusion_lift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (p r n : ℕ) (h : 2 * p + r = n) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map (mixedLevelInclusion k A p r n h) ≫
        (connesMixedTotalLiftIso.{lift} k A).hom.f n =
      mixedLevelInclusionLift.{lift} k A p r n h := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let R := connesMixedBicomplex k A
  letI : ∀ m, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  let a := (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv
  let i := R.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj R
  have hι : U.map i ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom =
      P.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega) :=
    HomologicalComplex₂.map_ιTotal_functorTotalIsoComponent_hom U R p (r + p) n (by change p + (r + p) = n; omega)
  change U.map (a ≫ i) ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom =
    U.map a ≫ P.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  exact (congrArg (fun f => f ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom)
    (U.map_comp a i)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => U.map a ≫ f) hι))

/-- The positive inclusion x+sN is transported by the total comparisons. -/
def mixedToCyclicLift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)) ⟶
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ)) :=
  (connesMixedTotalLiftIso.{lift} k A).inv ≫
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (mixedToCyclic k A) ≫
        (cyclicTotalLiftIso.{lift} k A).hom

/-- The transported inclusion retains exactly the original positive chain map. -/
@[reassoc]
theorem map_mixedToCyclic_lift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (mixedToCyclic k A) ≫
          (cyclicTotalLiftIso.{lift} k A).hom =
      (connesMixedTotalLiftIso.{lift} k A).hom ≫ mixedToCyclicLift.{lift} k A := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let eM := connesMixedTotalLiftIso.{lift} k A
  let eC := cyclicTotalLiftIso.{lift} k A
  let i := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map (mixedToCyclic k A)
  change i ≫ eC.hom = eM.hom ≫ (eM.inv ≫ i ≫ eC.hom)
  exact (eM.hom_inv_id_assoc (i ≫ eC.hom)).symm

/-- Exact native lifting and the total isomorphisms preserve the positive inclusion. -/
instance mixedToCyclicLift_quasiIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    _root_.QuasiIso (mixedToCyclicLift.{lift} k A) := by
  letI : _root_.QuasiIso (mixedToCyclic k A) := mixedToCyclic_quasiIso k A
  unfold mixedToCyclicLift
  infer_instance

/-- The lifted positive inclusion induces the lifted mixed-to-cyclic homology comparison. -/
def mixedCyclicHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).homology n ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ)).homology n :=
  asIso (HomologicalComplex.homologyMap (mixedToCyclicLift.{lift} k A) n)

/-- Its forward map is exactly homology of the transported original positive inclusion. -/
theorem mixedCyclicHomologyLiftIso_hom.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (mixedCyclicHomologyLiftIso.{lift} k A n).hom =
      HomologicalComplex.homologyMap (mixedToCyclicLift.{lift} k A) n := rfl

/-- Supported original bar coordinates detect maps from the lifted mixed total. -/
theorem connesMixedTotalLift_hom_ext.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    {X : ModuleCat.{max lift ground algebra} k} (n : ℕ)
    {f g : ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).X n ⟶ X}
    (h : ∀ p r (hr : 2 * p + r = n),
      mixedLevelInclusionLift.{lift} k A p r n hr ≫ f =
        mixedLevelInclusionLift.{lift} k A p r n hr ≫ g) : f = g := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)
  apply HomologicalComplex₂.total.hom_ext
  intro p q hn
  by_cases hpq : p ≤ q
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = r + p :=
      ⟨q - p, (Nat.sub_add_cancel hpq).symm⟩
    have hr : 2 * p + r = n := by
      change p + (r + p) = n at hn
      omega
    let e₀ := ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
    let e : (P.X p).X (r + p) ≅ U.obj ((bComplex k A).X r) := U.mapIso e₀
    let ι : (P.X p).X (r + p) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotal (ComplexShape.down ℕ) p (r + p) n hn
    have he : e.inv = U.map e₀.inv := Functor.mapIso_inv U e₀
    apply (cancel_epi e.inv).1
    have hValue := h p r hr
    change (U.map e₀.inv ≫ ι) ≫ f = (U.map e₀.inv ≫ ι) ≫ g at hValue
    change e.inv ≫ ι ≫ f = e.inv ≫ ι ≫ g
    rw [he]
    exact (Category.assoc (U.map e₀.inv) ι f).symm.trans
      (hValue.trans (Category.assoc (U.map e₀.inv) ι g))
  · have hZero : IsZero ((P.X p).X q) :=
      Functor.map_isZero U
        (ChainComplex.mixedBicomplex_isZero_cell (bComplex k A) (connesBoundaryHomotopy k A)
          (fun j => by simpa only [connesBoundaryHomotopy_hom] using
            connesBoundary_square k A j) p q (by omega))
    exact hZero.eq_of_src _ _

/-- Every supported lifted level keeps the original even term and the positive inserted norm. -/
theorem mixedToCyclicLift_inclusion.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (p r n : ℕ) (h : 2 * p + r = n) :
    let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
    let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
    let even : U.obj (chainLevel k A A r) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
    let odd : U.obj (chainLevel k A A (r + 1)) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    mixedLevelInclusionLift.{lift} k A p r n h ≫ (mixedToCyclicLift.{lift} k A).f n =
      even + U.map (normMap k A r) ≫ U.map (extraDegeneracy k A r) ≫ odd := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let RM := connesMixedBicomplex k A
  let RC := cyclicBicomplex k A
  let PM : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RM
  let PC : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RC
  let eM := connesMixedTotalLiftIso.{lift} k A
  let eC := cyclicTotalLiftIso.{lift} k A
  let M := (HomologicalComplex.eval _ (ComplexShape.down ℕ) n).mapIso eM
  let C := (HomologicalComplex.eval _ (ComplexShape.down ℕ) n).mapIso eC
  let v := mixedLevelInclusion k A p r n h
  let i := (mixedToCyclic k A).f n
  let even : chainLevel k A A r ⟶ (RC.total (ComplexShape.down ℕ)).X n :=
    RC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let odd : chainLevel k A A (r + 1) ⟶ (RC.total (ComplexShape.down ℕ)).X n :=
    RC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let evenL : U.obj (chainLevel k A A r) ⟶ (PC.total (ComplexShape.down ℕ)).X n :=
    PC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddL : U.obj (chainLevel k A A (r + 1)) ⟶ (PC.total (ComplexShape.down ℕ)).X n :=
    PC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let N := normMap k A r
  let s := extraDegeneracy k A r
  have hI : v ≫ i = even + N ≫ s ≫ odd := by
    have hImage : v ≫ mixedToCyclicComponent k A n = even + N ≫ s ≫ odd :=
      mixedToCyclicComponent_inclusion k A p r n h
    have hi : i = mixedToCyclicComponent k A n := mixedToCyclic_f k A n
    exact (congrArg (fun a : (connesMixedTotal k A).X n ⟶ (cyclicTotal k A).X n =>
      v ≫ a) hi).trans hImage
  have hv : U.map v ≫ M.hom = mixedLevelInclusionLift.{lift} k A p r n h :=
    map_mixedLevelInclusion_lift k A p r n h
  have hField : (mixedToCyclicLift.{lift} k A).f n = M.inv ≫ U.map i ≫ C.hom := rfl
  have he : U.map even ≫ C.hom = evenL :=
    map_cyclicInclusionOrZero_lift k A (2 * p) r n
  have ho : U.map odd ≫ C.hom = oddL :=
    map_cyclicInclusionOrZero_lift k A (2 * p - 1) (r + 1) n
  change mixedLevelInclusionLift.{lift} k A p r n h ≫ (mixedToCyclicLift.{lift} k A).f n =
    evenL + U.map N ≫ U.map s ≫ oddL
  calc
    _ = (U.map v ≫ M.hom) ≫ (M.inv ≫ U.map i ≫ C.hom) :=
      congrArg₂ (fun a b => a ≫ b) hv.symm hField
    _ = U.map (v ≫ i) ≫ C.hom := by
      rw [U.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = U.map (even + N ≫ s ≫ odd) ≫ C.hom :=
      congrArg (fun f => U.map f ≫ C.hom) hI
    _ = (U.map even ≫ C.hom) + U.map N ≫ U.map s ≫ (U.map odd ≫ C.hom) := by
      rw [U.map_add, U.map_comp, U.map_comp]
      simp only [Preadditive.add_comp, Category.assoc]
    _ = _ := congrArg₂ (fun a b => a + b) he
      (congrArg (fun f => U.map N ≫ U.map s ≫ f) ho)

/-- Native lifting of the original boundary earns square-zero in the original carrier world. -/
theorem connesBoundaryHomotopyLift_square.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (connesBoundaryHomotopyLift.{ground, algebra, lift} k A).hom n (n + 1) ≫
      (connesBoundaryHomotopyLift.{ground, algebra, lift} k A).hom (n + 1) (n + 2) = 0 := by
  rw [connesBoundaryHomotopyLift_hom, connesBoundaryHomotopyLift_hom,
    ← Functor.map_comp, connesBoundary_square, Functor.map_zero]

/-- The original lifted b/B data form the canonical mixed object in the shared carrier. -/
def connesMixedComplexModelLift.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] : MixedComplex (ModuleCat.{max ground algebra lift} k) :=
  MixedComplex.ofBoundaryHomotopy
    (((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k A))
    (connesBoundaryHomotopyLift.{ground, algebra, lift} k A)
    (connesBoundaryHomotopyLift_square.{ground, algebra, lift} k A)

/-- The lifted canonical object retains the complete original lifted b-complex. -/
@[simp]
theorem connesMixedComplexModelLift_underlying.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    (connesMixedComplexModelLift.{ground, algebra, lift} k A).underlying =
      ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (bComplex k A) := rfl

/-- Its operator is the native lift of the original Connes B. -/
@[simp]
theorem connesMixedComplexModelLift_B.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (connesMixedComplexModelLift.{ground, algebra, lift} k A).B n =
      (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map (connesBoundary k A n) :=
  connesBoundaryHomotopyLift_hom k A n

section MixedNaturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The original independent-carrier algebra map is an canonical mixed-complex morphism.
Unit compatibility is explicit because the original Connes B uses the unit insertion. -/
def connesMixedComplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    connesMixedComplexModelLift.{u, v, w} k A ⟶ connesMixedComplexModelLift.{u, w, v} k B :=
  MixedComplex.ofBoundaryHomotopyMap (connesBoundaryHomotopyLift.{u, v, w} k A)
    (connesBoundaryHomotopyLift_square.{u, v, w} k A)
    (connesBoundaryHomotopyLift.{u, w, v} k B)
    (connesBoundaryHomotopyLift_square.{u, w, v} k B)
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne)

/-- The canonical mixed map preserves the original full tensor-level chain map. -/
@[simp]
theorem connesMixedComplexMapLift_underlying (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (connesMixedComplexMapLift f hOne).underlying = bComplexMapLift f := rfl

/-- The independent-world raw mixed map transports the column coordinates. -/
def connesMixedBicomplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A) ⟶
      (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := bComplex k A
  let L := bComplex k B
  let H₀A := connesBoundaryHomotopy k A
  let H₀B := connesBoundaryHomotopy k B
  let HA := connesBoundaryHomotopyLift.{u, v, w} k A
  let HB := connesBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ n, H₀A.hom n (n + 1) ≫ H₀A.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀A]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n
  let hB : ∀ n, H₀B.hom n (n + 1) ≫ H₀B.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀B]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k B n
  let hcA : ∀ n, HA.hom n (n + 1) = UA.map (H₀A.hom n (n + 1)) := fun n =>
    (connesBoundaryHomotopyLift_hom k A n).trans
      (congrArg (fun a => UA.map a) (connesBoundaryHomotopy_hom k A n).symm)
  let hcB : ∀ n, HB.hom n (n + 1) = UB.map (H₀B.hom n (n + 1)) := fun n =>
    (connesBoundaryHomotopyLift_hom k B n).trans
      (congrArg (fun a => UB.map a) (connesBoundaryHomotopy_hom k B n).symm)
  exact ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (connesMixedComplexMapLift f hOne).underlying
    (fun n => (connesMixedComplexMapLift f hOne).comm_B n)

/-- Every supported mixed component keeps the original bar map in its native coordinates. -/
theorem connesMixedBicomplexMapLift_component (f : A →ₙₐ[k] B) (hOne : f 1 = 1)
    (p n q : ℕ) (h : n + p = q) :
    ((connesMixedBicomplexMapLift f hOne).f p).f q =
      (ModuleCat.uliftFunctor.{w, max u v} k).map
          (ChainComplex.mixedColumnIso (bComplex k A) p n q h).hom ≫
        (bComplexMapLift f).f n ≫
          (ModuleCat.uliftFunctor.{v, max u w} k).map
            (ChainComplex.mixedColumnIso (bComplex k B) p n q h).inv := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := bComplex k A
  let L := bComplex k B
  let H₀A := connesBoundaryHomotopy k A
  let H₀B := connesBoundaryHomotopy k B
  let HA := connesBoundaryHomotopyLift.{u, v, w} k A
  let HB := connesBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ j, H₀A.hom j (j + 1) ≫ H₀A.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀A]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A j
  let hB : ∀ j, H₀B.hom j (j + 1) ≫ H₀B.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀B]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k B j
  let hcA : ∀ j, HA.hom j (j + 1) = UA.map (H₀A.hom j (j + 1)) := fun j =>
    (connesBoundaryHomotopyLift_hom k A j).trans
      (congrArg (fun a => UA.map a) (connesBoundaryHomotopy_hom k A j).symm)
  let hcB : ∀ j, HB.hom j (j + 1) = UB.map (H₀B.hom j (j + 1)) := fun j =>
    (connesBoundaryHomotopyLift_hom k B j).trans
      (congrArg (fun a => UB.map a) (connesBoundaryHomotopy_hom k B j).symm)
  change ((ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne)).f p).f q = _
  exact ChainComplex.mixedBicomplexFunctorMap_component UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne) p n q h

/-- The preserved finite-diagonal coproducts transport the raw mixed total map. -/
def connesMixedTotalMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedTotal k A) ⟶
        ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (connesMixedTotal k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let RA := connesMixedBicomplex k A
  let RB := connesMixedBicomplex k B
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RA
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RB
  letI : ∀ m, PreservesColimit (Discrete.functor
      (RA.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) UA := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  letI : ∀ m, PreservesColimit (Discrete.functor
      (RB.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) UB := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  let eA : (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k A) ≅ PA.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.functorTotalIso UA RA
  let eB : (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k B) ≅ PB.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.functorTotalIso UB RB
  let φ : PA ⟶ PB := connesMixedBicomplexMapLift f hOne
  let m : PA.total (ComplexShape.down ℕ) ⟶ PB.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  exact eA.hom ≫ m ≫ eB.inv

/-- The native total of the raw map applies the bar map in every supported coordinate. -/
theorem connesMixedBicomplexMapLift_inclusion (f : A →ₙₐ[k] B) (hOne : f 1 = 1)
    (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusionLift.{w} k A p r n h ≫
        (HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ)).f n =
      (bComplexMapLift f).f r ≫ mixedLevelInclusionLift.{v} k B p r n h := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k B)
  let φ : PA ⟶ PB := connesMixedBicomplexMapLift f hOne
  let m := HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  let a : (PA.X p).X (r + p) ≅ UA.obj ((bComplex k A).X r) :=
    UA.mapIso (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl)
  let b : (PB.X p).X (r + p) ≅ UB.obj ((bComplex k B).X r) :=
    UB.mapIso (ChainComplex.mixedColumnIso (bComplex k B) p r (r + p) rfl)
  let v : UA.obj ((bComplex k A).X r) ⟶ UB.obj ((bComplex k B).X r) :=
    (bComplexMapLift f).f r
  let ιA : (PA.X p).X (r + p) ⟶ (PA.total (ComplexShape.down ℕ)).X n :=
    PA.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  let ιB : (PB.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n :=
    PB.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  have hι : ιA ≫ m.f n = (φ.f p).f (r + p) ≫ ιB :=
    HomologicalComplex₂.ιTotal_map PA PB φ (ComplexShape.down ℕ)
      p (r + p) n (by change p + (r + p) = n; omega)
  have hφ : (φ.f p).f (r + p) = a.hom ≫ v ≫ b.inv :=
    connesMixedBicomplexMapLift_component f hOne p r (r + p) rfl
  change (a.inv ≫ ιA) ≫ m.f n = v ≫ (b.inv ≫ ιB)
  calc
    (a.inv ≫ ιA) ≫ m.f n = a.inv ≫ (ιA ≫ m.f n) := Category.assoc _ _ _
    _ = a.inv ≫ ((φ.f p).f (r + p) ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n =>
        a.inv ≫ x) hι
    _ = a.inv ≫ ((a.hom ≫ v ≫ b.inv) ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.X p).X (r + p) =>
        a.inv ≫ (x ≫ ιB)) hφ
    _ = a.inv ≫ (a.hom ≫ v ≫ b.inv ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n =>
        a.inv ≫ x)
        ((Category.assoc a.hom (v ≫ b.inv) ιB).trans
          (congrArg (fun x : UA.obj ((bComplex k A).X r) ⟶
              (PB.total (ComplexShape.down ℕ)).X n => a.hom ≫ x)
            (Category.assoc v b.inv ιB)))
    _ = v ≫ b.inv ≫ ιB := a.inv_hom_id_assoc (v ≫ b.inv ≫ ιB)


omit [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B] in
/-- Unit preservation is needed only to specialize the insertion vector to the target unit. -/
theorem normInsertMapLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    levelMapLift (f : A →ₗ[k] B) n ≫
        (ModuleCat.uliftFunctor.{v, max u w} k).map (normMap k B n) ≫
          (ModuleCat.uliftFunctor.{v, max u w} k).map (extraDegeneracy k B n) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map (normMap k A n) ≫
        (ModuleCat.uliftFunctor.{w, max u v} k).map (extraDegeneracy k A n) ≫
          levelMapLift (f : A →ₗ[k] B) (n + 1) := by
  have hVector : (f : A →ₗ[k] B) (1 : A) = (1 : B) := hOne
  simpa only [extraDegeneracy, hVector, Functor.map_comp, Category.assoc] using
    normInsertWithMapLift_naturality (f : A →ₗ[k] B) (1 : A) n

/-- The positive I intertwines the original raw mixed and cyclic maps in independent worlds. -/
theorem mixedToCyclicLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
        (ComplexShape.down ℕ) ≫ mixedToCyclicLift.{v} k B =
      mixedToCyclicLift.{w} k A ≫
        HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let CA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  let CB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k B)
  let m := HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
    (ComplexShape.down ℕ)
  let c := HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)
  let I := mixedToCyclicLift.{w} k A
  let I' := mixedToCyclicLift.{v} k B
  apply HomologicalComplex.hom_ext
  intro n
  apply connesMixedTotalLift_hom_ext.{w} k A n
  intro p r h
  let ιA := mixedLevelInclusionLift.{w} k A p r n h
  let ιB := mixedLevelInclusionLift.{v} k B p r n h
  let evenA : UA.obj (chainLevel k A A r) ⟶
      (CA.total (ComplexShape.down ℕ)).X n :=
    CA.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddA : UA.obj (chainLevel k A A (r + 1)) ⟶
      (CA.total (ComplexShape.down ℕ)).X n :=
    CA.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let evenB : UB.obj (chainLevel k B B r) ⟶
      (CB.total (ComplexShape.down ℕ)).X n :=
    CB.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddB : UB.obj (chainLevel k B B (r + 1)) ⟶
      (CB.total (ComplexShape.down ℕ)).X n :=
    CB.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let a := levelMapLift (f : A →ₗ[k] B) r
  let a' := levelMapLift (f : A →ₗ[k] B) (r + 1)
  let NA := UA.map (normMap k A r)
  let NB := UB.map (normMap k B r)
  let sA := UA.map (extraDegeneracy k A r)
  let sB := UB.map (extraDegeneracy k B r)
  have hI : ιA ≫ I.f n = evenA + NA ≫ sA ≫ oddA :=
    mixedToCyclicLift_inclusion k A p r n h
  have hI' : ιB ≫ I'.f n = evenB + NB ≫ sB ≫ oddB :=
    mixedToCyclicLift_inclusion k B p r n h
  have hm : ιA ≫ m.f n = a ≫ ιB :=
    (connesMixedBicomplexMapLift_inclusion f hOne p r n h).trans
      (congrArg (fun x => x ≫ ιB) (bComplexMapLift_f f r))
  have he : evenA ≫ c.f n = a ≫ evenB := cyclicBicomplexMap_ιTotalOrZero f (2 * p) r n
  have ho : oddA ≫ c.f n = a' ≫ oddB :=
    cyclicBicomplexMap_ιTotalOrZero f (2 * p - 1) (r + 1) n
  have hSN : a ≫ NB ≫ sB = NA ≫ sA ≫ a' := normInsertMapLift_naturality f hOne r
  have hPost : NA ≫ sA ≫ (a' ≫ oddB) = a ≫ NB ≫ sB ≫ oddB := by
    calc
      NA ≫ sA ≫ (a' ≫ oddB) = (NA ≫ sA ≫ a') ≫ oddB := by
        simp only [Category.assoc]
      _ = (a ≫ NB ≫ sB) ≫ oddB :=
        congrArg (fun x : UA.obj (chainLevel k A A r) ⟶
          UB.obj (chainLevel k B B (r + 1)) => x ≫ oddB) hSN.symm
      _ = a ≫ NB ≫ sB ≫ oddB := by
        simp only [Category.assoc]
  have hLeft : ιA ≫ (m.f n ≫ I'.f n) =
      a ≫ evenB + a ≫ NB ≫ sB ≫ oddB := by
    calc
      _ = (a ≫ ιB) ≫ I'.f n :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ I'.f n) hm)
      _ = a ≫ (evenB + NB ≫ sB ≫ oddB) :=
        (Category.assoc _ _ _).trans (congrArg (fun x => a ≫ x) hI')
      _ = _ := by simp only [Preadditive.comp_add, Category.assoc]
  have hRight : ιA ≫ (I.f n ≫ c.f n) =
      a ≫ evenB + a ≫ NB ≫ sB ≫ oddB := by
    calc
      _ = (evenA + NA ≫ sA ≫ oddA) ≫ c.f n :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ c.f n) hI)
      _ = evenA ≫ c.f n + NA ≫ sA ≫ (oddA ≫ c.f n) := by
        simp only [Preadditive.add_comp, Category.assoc]
      _ = a ≫ evenB + NA ≫ sA ≫ (a' ≫ oddB) :=
        congrArg₂ (fun x y => x + y) he (congrArg (fun x => NA ≫ sA ≫ x) ho)
      _ = _ := congrArg (fun x => a ≫ evenB + x) hPost
  change ιA ≫ (m.f n ≫ I'.f n) = ιA ≫ (I.f n ≫ c.f n)
  exact hLeft.trans hRight.symm

end MixedNaturality

end ModuleCat.Algebra.Hochschild.NonUnital
