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
# Independent-world naturality of the lifted Connes comparison

Let k be a commutative ring and A a nonunital k-algebra with k-bilinear
multiplication. At H = max(u,v,z), the first-column cokernel projection
gives p_A^H : Tot(D_A^H) → Cλ_A^H. It projects column zero and
annihilates the positive columns. On homology, the universe-lift
comparison supplies a map ULift^H HC_n(A) → H_n(Cλ_A^H).

For a nonunital k-algebra map f : A → B, with A and B in independent
worlds v and w, put H = max(u,v,w,z). The chain and homology squares
commute: p_B^H ∘ Tot(f) = Cλ^H(f) ∘ p_A^H.
If k is a ℚ-algebra, the homology projection is the forward map of
the rational comparison isomorphism. Its inverse satisfies the
corresponding square H_n(Cλ_A^H) → ULift^H HC_n(B).
No unit-preservation or equality of the coefficient worlds is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- For a commutative ring k, a nonunital k-algebra A with
k-bilinear multiplication and H = max(u,v,z), the first-column
cokernel projection is the chain map Tot(D_A^H) → Cλ_A^H.
In total degree n it projects the summand (0,n) to the Connes
quotient and is zero on every summand (p,q) with p > 0. -/
def cyclicToConnesAtHeight :
    HomologicalComplex₂.total (cyclicBicomplexAtHeight.{u,v,z} k A) (ComplexShape.down ℕ) ⟶
      connesComplexAtHeight.{u,v,z} k A :=
  HomologicalComplex₂.firstColumnCokernelProjection (cyclicBicomplexAtHeight.{u,v,z} k A)

/-- For a nonunital k-algebra A and H = max(u,v,z), the map
ULift^H HC_n(A) → H_n(Cλ_A^H) first identifies lifted cyclic homology
with the homology of the lifted cyclic total, then applies the
homology map of its first-column projection. This map is defined
over any commutative ground ring k. -/
def cyclicToConnesHomologyAtHeight (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj (cyclicHomology k A n) ⟶
      connesHomologyAtHeight.{u,v,z} k A n :=
  (cyclicHomologyLiftIso.{max u v z} k A n).hom ≫
    HomologicalComplex.homologyMap (cyclicToConnesAtHeight.{u,v,z} k A) n

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- For a nonunital k-algebra map f : A → B, with k, A and B
in independent worlds u, v and w, put H = max(u,v,w,z).
The chain maps satisfy p_B^H ∘ Tot(f) = Cλ^H(f) ∘ p_A^H from
the lifted cyclic total of A to the lifted Connes complex of B.
The multiplication in both algebras is k-bilinear. -/
@[reassoc]
theorem cyclicToConnesAtHeight_naturality (f : A →ₙₐ[k] B) :
    cyclicTotalMapAtHeight.{u,v,w,z} f ≫ cyclicToConnesAtHeight.{u,w,max u v w z} k B =
      cyclicToConnesAtHeight.{u,v,max u v w z} k A ≫
        connesComplexHomAtHeight.{u,v,w,z} k A f :=
  HomologicalComplex₂.firstColumnCokernelProjection_naturality
    (cyclicBicomplexMapAtHeight.{u,v,w,z} f)

/-- For a nonunital k-algebra map f : A → B and n ≥ 0, put all
objects at H = max(u,v,w,z). The homology projections satisfy
p_(B,n)^H ∘ HC_n^H(f) = H_n(Cλ^H(f)) ∘ p_(A,n)^H from
ULift^H HC_n(A) to H_n(Cλ_B^H).
The carrier worlds of A and B are independent. -/
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

/-- For a commutative ℚ-algebra k, a nonunital k-algebra A with
k-bilinear multiplication and H = max(u,v,z), the forward map of
ULift^H HC_n(A) ≅ H_n(Cλ_A^H) equals the chosen-height homology
map of the first-column projection, for every n ≥ 0. -/
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

/-- For a commutative ℚ-algebra k, a nonunital k-algebra map
f : A → B and n ≥ 0, let χ_A^H and χ_B^H be the rational
comparison isomorphisms at H = max(u,v,w,z). Their forward maps
satisfy χ_B^H.hom ∘ HC_n^H(f) = H_n(Cλ^H(f)) ∘ χ_A^H.hom.
The square has source ULift^H HC_n(A) and target H_n(Cλ_B^H). -/
@[reassoc]
theorem cyclicToConnesHomologyIsoAtHeight_hom_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMapAtHeight.{u,v,w,z} f n ≫
        (cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z} k B n).hom =
      (cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z} k A n).hom ≫
        connesHomologyMapAtHeight.{u,v,w,z} k A f n := by
  rw [cyclicToConnesHomologyIsoAtHeight_hom_eq, cyclicToConnesHomologyIsoAtHeight_hom_eq]
  exact cyclicToConnesHomologyAtHeight_naturality.{u,v,w,z} f n

/-- For a commutative ℚ-algebra k, a nonunital k-algebra map
f : A → B and n ≥ 0, the inverse comparison maps at
H = max(u,v,w,z) satisfy
(χ_B^H)⁻¹ ∘ H_n(Cλ^H(f)) = HC_n^H(f) ∘ (χ_A^H)⁻¹.
This square goes from H_n(Cλ_A^H) to ULift^H HC_n(B) and retains
the independent carrier worlds of both algebras. -/
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
