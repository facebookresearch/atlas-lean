/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.BicomplexFirstColumnMap
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesComparisonWorkingHeight

/-!
# Naturality of lifted Connes comparisons

The first-column projection of a lifted cyclic
bicomplex defines the comparison and its coefficient
square over the ground ring. In the rational setting
it is the hom of the cyclic-to-Connes isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The first-column total projection at the chosen working height. -/
def cyclicToConnesAtHeight :
    HomologicalComplex₂.total (cyclicBicomplexAtHeight.{u,v,z} k A) (ComplexShape.down ℕ) ⟶
      connesComplexAtHeight.{u,v,z} k A :=
  HomologicalComplex₂.firstColumnCokernelProjection (cyclicBicomplexAtHeight.{u,v,z} k A)

/-- The prescribed lifted HC map followed by the first-column projection on native homology. -/
def cyclicToConnesHomologyAtHeight (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj (cyclicHomology k A n) ⟶
      connesHomologyAtHeight.{u,v,z} k A n :=
  (cyclicHomologyLiftIso.{max u v z} k A n).hom ≫
    HomologicalComplex.homologyMap (cyclicToConnesAtHeight.{u,v,z} k A) n

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The native total and incoming-cokernel maps preserve the projection across coefficient worlds. -/
@[reassoc]
theorem cyclicToConnesAtHeight_naturality (f : A →ₙₐ[k] B) :
    cyclicTotalMapAtHeight.{u,v,w,z} f ≫ cyclicToConnesAtHeight.{u,w,max u v w z} k B =
      cyclicToConnesAtHeight.{u,v,max u v w z} k A ≫
        connesComplexHomAtHeight.{u,v,w,z} k A f :=
  HomologicalComplex₂.firstColumnCokernelProjection_naturality
    (cyclicBicomplexMapAtHeight.{u,v,w,z} f)

/-- The homology projection retains its coefficient square at the common height. -/
@[reassoc]
theorem cyclicToConnesHomologyAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMapAtHeight.{u,v,w,z} f n ≫
        cyclicToConnesHomologyAtHeight.{u,w,max u v w z} k B n =
      cyclicToConnesHomologyAtHeight.{u,v,max u v w z} k A n ≫
        connesHomologyMapAtHeight.{u,v,w,z} k A f n := by
  let eA := cyclicHomologyLiftIso.{max u v w z} k A n
  let eB := cyclicHomologyLiftIso.{max u v w z} k B n
  let m := HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n
  let pA := HomologicalComplex.homologyMap
    (cyclicToConnesAtHeight.{u,v,max u v w z} k A) n
  let pB := HomologicalComplex.homologyMap
    (cyclicToConnesAtHeight.{u,w,max u v w z} k B) n
  let q := connesHomologyMapAtHeight.{u,v,w,z} k A f n
  have h : m ≫ pB = pA ≫ q := by
    have hn := congrArg
      (fun g : HomologicalComplex₂.total (cyclicBicomplexAtHeight.{u,v,max u v w z} k A)
          (ComplexShape.down ℕ) ⟶ connesComplexAtHeight.{u,w,max u v w z} k B =>
        HomologicalComplex.homologyMap g n)
      (cyclicToConnesAtHeight_naturality.{u,v,w,z} f)
    simp only [HomologicalComplex.homologyMap_comp] at hn
    exact hn
  change (eA.hom ≫ m ≫ eB.inv) ≫ (eB.hom ≫ pB) = (eA.hom ≫ pA) ≫ q
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun g => eA.hom ≫ g) h

variable (k A)

section Rational

variable [Algebra ℚ k]

/-- The native first-column projection is the exact hom of the prescribed rational comparison. -/
theorem cyclicToConnesHomologyIsoAtHeight_hom_eq (n : ℕ) :
    (cyclicToConnesHomologyIsoAtHeight.{u,v,z} k A n).hom =
      cyclicToConnesHomologyAtHeight.{u,v,z} k A n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let K := cyclicBicomplex k A
  let : ∀ m, PreservesColimit
      (Discrete.functor (K.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U :=
    fun m => by
      let : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
        Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
          simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
      infer_instance
  let eT := HomologicalComplex₂.functorTotalIso U K
  let eQ := connesComplexLiftIsoAtHeight.{u,v,z} k A
  let χT := (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app (cyclicTotal k A)
  let χQ := (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app (connesComplex k A)
  let p := cyclicToConnes k A
  let p' := cyclicToConnesAtHeight.{u,v,z} k A
  let hp := HomologicalComplex.homologyMap
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map p) n
  let hq := HomologicalComplex.homologyMap eQ.hom n
  let ht := HomologicalComplex.homologyMap eT.hom n
  let hp' := HomologicalComplex.homologyMap p' n
  have hχ : U.map (HomologicalComplex.homologyMap p n) ≫ χQ.inv = χT.inv ≫ hp :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).inv.naturality p
  have hSquare : hp ≫ hq = ht ≫ hp' := by
    have h := HomologicalComplex₂.firstColumnCokernelProjection_map U K
    have hn := congrArg
      (fun f : (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicTotal k A) ⟶
          connesComplexAtHeight.{u,v,z} k A => HomologicalComplex.homologyMap f n) h
    simp only [HomologicalComplex.homologyMap_comp] at hn
    exact hn
  have hLift : (cyclicHomologyLiftIso.{max u v z} k A n).hom = χT.inv ≫ ht := rfl
  rw [cyclicToConnesHomologyIsoAtHeight_hom]
  change (U.map (HomologicalComplex.homologyMap p n) ≫ χQ.inv) ≫ hq =
    (cyclicHomologyLiftIso.{max u v z} k A n).hom ≫ hp'
  have hAll : (U.map (HomologicalComplex.homologyMap p n) ≫ χQ.inv) ≫ hq =
      (χT.inv ≫ ht) ≫ hp' :=
    (congrArg (fun f => f ≫ hq) hχ).trans
      ((Category.assoc χT.inv hp hq).trans
        ((congrArg (fun f => χT.inv ≫ f) hSquare).trans
          (Category.assoc χT.inv ht hp').symm))
  exact hAll.trans (congrArg (fun f => f ≫ hp') hLift.symm)

/-- The prescribed rational comparison itself preserves the independent-world coefficient maps. -/
@[reassoc]
theorem cyclicToConnesHomologyIsoAtHeight_hom_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMapAtHeight.{u,v,w,z} f n ≫
        (cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z} k B n).hom =
      (cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z} k A n).hom ≫
        connesHomologyMapAtHeight.{u,v,w,z} k A f n := by
  rw [cyclicToConnesHomologyIsoAtHeight_hom_eq, cyclicToConnesHomologyIsoAtHeight_hom_eq]
  exact cyclicToConnesHomologyAtHeight_naturality.{u,v,w,z} f n

/-- The inverse rational comparison preserves the same independent-world coefficient square. -/
@[reassoc]
theorem cyclicToConnesHomologyIsoAtHeight_inv_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    connesHomologyMapAtHeight.{u,v,w,z} k A f n ≫
        (cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z} k B n).inv =
      (cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z} k A n).inv ≫
        cyclicHomologyMapAtHeight.{u,v,w,z} f n := by
  let eA := cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z} k A n
  let eB := cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z} k B n
  let m := cyclicHomologyMapAtHeight.{u,v,w,z} f n
  let q := connesHomologyMapAtHeight.{u,v,w,z} k A f n
  have h : m ≫ eB.hom = eA.hom ≫ q :=
    cyclicToConnesHomologyIsoAtHeight_hom_naturality.{u,v,w,z} k A f n
  apply (cancel_mono eB.hom).1
  calc
    (q ≫ eB.inv) ≫ eB.hom = q := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (eA.inv ≫ m) ≫ eB.hom := by
      symm
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => eA.inv ≫ f) h).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ q) eA.inv_hom_id).trans (Category.id_comp q))))

end Rational

end ModuleCat.Algebra.Hochschild.NonUnital
