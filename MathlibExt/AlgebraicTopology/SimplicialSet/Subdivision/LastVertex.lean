/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Iterate

/-!
# The last-vertex map from simplicial subdivision

This file constructs the classical natural transformation from Kan
subdivision to the identity functor on simplicial sets.  On a vertex of the
subdivision of a standard simplex, it takes the maximum of the corresponding
nonempty finite chain of vertices.

No nonsingularity, finiteness, realization, homotopy, or weak-equivalence
claim is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SimplexCategory

/-- The last vertex of a nonempty finite chain in a finite ordinal. -/
def sdChainLast (n : SimplexCategory)
    (S : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1)))) :
    ULift.{u} (Fin (n.len + 1)) :=
  S.finset.max' S.nonempty

/-- Taking the last vertex is monotone under inclusion of chains. -/
def sdLastVertexOrderHom (n : SimplexCategory) :
    PartialOrder.NonemptyFiniteChains
        (ULift.{u} (Fin (n.len + 1))) →o
      ULift.{u} (Fin (n.len + 1)) where
  toFun := sdChainLast n
  monotone' A _B h := Finset.max'_subset A.nonempty h

/-- The singleton chain at one vertex of a finite ordinal. -/
def sdSingletonChain (n : SimplexCategory) (i : Fin (n.len + 1)) :
    PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1))) where
  finset := {ULift.up i}
  comparable _ _ := Or.inl (by simp)

@[simp]
theorem sdChainLast_singleton (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    sdChainLast n (sdSingletonChain n i) = ULift.up i := by
  simp [sdChainLast, sdSingletonChain]

/-- Last vertex commutes with every monotone map of finite ordinals. -/
theorem sdChainLast_map {m n : SimplexCategory} (f : m ⟶ n)
    (S : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (m.len + 1)))) :
    sdChainLast n (S.map
        ((SimplexCategory.toPartOrd.map f).hom :
          ULift.{u} (Fin (m.len + 1)) →o
            ULift.{u} (Fin (n.len + 1)))) =
      (SimplexCategory.toPartOrd.map f).hom (sdChainLast m S) := by
  classical
  let _ : DecidableEq (ULift.{u} (Fin (n.len + 1))) :=
    Classical.decEq _
  unfold sdChainLast PartialOrder.NonemptyFiniteChains.map
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (SimplexCategory.toPartOrd.map f).hom.monotone
      (Finset.le_max' S.finset x hx)
  · apply Finset.le_max'
    exact Finset.mem_image.mpr
      ⟨S.finset.max' S.nonempty,
        Finset.max'_mem S.finset S.nonempty, rfl⟩

/-- The representable last-vertex map on one standard simplex. -/
def sdRepresentableLastVertexApp (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ SSet.stdSimplex.{u}.obj n :=
  PartOrd.nerveFunctor.map
      (PartOrd.ofHom (sdLastVertexOrderHom n)) ≫
    (SSet.stdSimplex.isoNerve n.len).inv

/-- The representable last-vertex map, natural in the standard simplex. -/
def lastVertex :
    SimplexCategory.sd.{u} ⟶ SSet.stdSimplex.{u} where
  app := sdRepresentableLastVertexApp
  naturality {m n} f := by
    ext d S
    apply SSet.stdSimplex.ext
    intro i
    change (sdChainLast n ((S.obj i).map
        ((SimplexCategory.toPartOrd.map f).hom :
          ULift.{u} (Fin (m.len + 1)) →o
            ULift.{u} (Fin (n.len + 1))))).down =
      f (sdChainLast m (S.obj i)).down
    exact congrArg ULift.down (sdChainLast_map f (S.obj i))

/-- On every coordinate of a subdivision simplex, the representable
last-vertex map takes the maximum of the corresponding chain. -/
@[simp]
theorem lastVertex_app_objEquiv_apply
    (n : SimplexCategory) {d : ℕ}
    (S : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (i : Fin (d + 1)) :
    SSet.stdSimplex.objEquiv
        ((lastVertex.app n).app (op ⦋d⦌) S) i =
      (sdChainLast n (S.obj i)).down := by
  rfl

end SimplexCategory

namespace SSet

/-- The natural last-vertex map from Kan subdivision to the identity functor. -/
noncomputable def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet.{u} :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv
    (𝟭 SSet) SimplexCategory.lastVertex

/-- On a standard simplex, the last-vertex map is the representable
last-vertex map after the canonical subdivision comparison. -/
theorem lastVertex_fac (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫
        SSet.lastVertex.app (SSet.stdSimplex.obj n) =
      SimplexCategory.lastVertex.app n := by
  exact SSet.sd.descOfIsLeftKanExtension_fac_app
    SSet.stdSimplex.sdIso.inv (𝟭 SSet)
      SimplexCategory.lastVertex n

/-- Vertex form of the representable characteristic law. -/
@[simp]
theorem lastVertex_stdSimplex_vertex (n : SimplexCategory)
    (S : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1)))) :
    (SSet.lastVertex.app (SSet.stdSimplex.obj n)).app (op ⦋0⦌)
        ((SSet.stdSimplex.sdIso.inv.app n).app (op ⦋0⦌)
          (ComposableArrows.mk₀ S)) =
      SSet.stdSimplex.obj₀Equiv.symm
        (SimplexCategory.sdChainLast n S).down := by
  have h := SSet.lastVertex_fac n
  exact congrArg
    (fun f => f.app (op ⦋0⦌) (ComposableArrows.mk₀ S)) h

/-- Coordinate form of the representable characteristic law. -/
@[simp]
theorem lastVertex_stdSimplex_apply (n : SimplexCategory) {d : ℕ}
    (S : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (i : Fin (d + 1)) :
    SSet.stdSimplex.objEquiv
        ((SSet.lastVertex.app (SSet.stdSimplex.obj n)).app (op ⦋d⦌)
          ((SSet.stdSimplex.sdIso.inv.app n).app (op ⦋d⦌) S)) i =
      (SimplexCategory.sdChainLast n (S.obj i)).down := by
  have h := SSet.lastVertex_fac n
  exact congrArg
    (fun f => SSet.stdSimplex.objEquiv
      (f.app (op ⦋d⦌) S) i) h

/-- The composite of `k` successive last-vertex maps. -/
noncomputable def sdIterLastVertex (X : SSet.{u}) (k : ℕ) :
    (SSet.sdIter k).obj X ⟶ X :=
  Nat.rec (motive := fun k => (SSet.sdIter k).obj X ⟶ X)
    (𝟙 X)
    (fun k ih => SSet.lastVertex.app ((SSet.sdIter k).obj X) ≫ ih) k

/-- The iterated last-vertex map at zero subdivisions is the identity. -/
@[simp]
theorem sdIterLastVertex_zero (X : SSet.{u}) :
    sdIterLastVertex X 0 = 𝟙 X :=
  rfl

/-- The iterated last-vertex map after one more subdivision begins with the
last-vertex map. -/
@[simp]
theorem sdIterLastVertex_succ (X : SSet.{u}) (k : ℕ) :
    sdIterLastVertex X (k + 1) =
      SSet.lastVertex.app ((SSet.sdIter k).obj X) ≫
        sdIterLastVertex X k :=
  rfl

/-- Iterated last-vertex maps are natural in the simplicial set. -/
@[reassoc]
theorem sdIterLastVertex_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    (SSet.sdIter k).map f ≫ sdIterLastVertex Y k =
      sdIterLastVertex X k ≫ f := by
  set_option backward.isDefEq.respectTransparency false in
    induction k with
    | zero => simp
    | succ k ih =>
        simp only [SSet.sdIter_map_succ, sdIterLastVertex_succ]
        rw [← Category.assoc, SSet.lastVertex.naturality]
        simp only [Functor.id_obj, Functor.id_map]
        rw [Category.assoc, ih, ← Category.assoc]

/-- The canonical subdivision vertex lying over a vertex of a simplicial set. -/
def sdVertexOfVertex {A : SSet.{u}} (x : A _⦋0⦌) :
    (SSet.sd.obj A) _⦋0⦌ :=
  (SSet.sd.map (SSet.yonedaEquiv.symm x)).app (op ⦋0⦌)
    ((SSet.stdSimplex.sdIso.inv.app ⦋0⦌).app (op ⦋0⦌)
      (ComposableArrows.mk₀
        (SimplexCategory.sdSingletonChain ⦋0⦌ 0)))

/-- The last-vertex map sends the canonical lift literally to its source
vertex. -/
@[simp]
theorem lastVertex_sdVertexOfVertex {A : SSet.{u}} (x : A _⦋0⦌) :
    (SSet.lastVertex.app A).app (op ⦋0⦌)
      (SSet.sdVertexOfVertex x) = x := by
  let v := (SSet.stdSimplex.sdIso.inv.app ⦋0⦌).app (op ⦋0⦌)
    (ComposableArrows.mk₀
      (SimplexCategory.sdSingletonChain ⦋0⦌ 0))
  have hnat := SSet.lastVertex.naturality
    (SSet.yonedaEquiv.symm x)
  have happ := congrArg
    (fun f => f.app (op ⦋0⦌) v) hnat
  change (SSet.lastVertex.app A).app _
      ((SSet.sd.map (SSet.yonedaEquiv.symm x)).app _ v) =
    (SSet.yonedaEquiv.symm x).app _
      ((SSet.lastVertex.app (Δ[0] : SSet.{u})).app _ v) at happ
  change (SSet.lastVertex.app A).app _
      ((SSet.sd.map (SSet.yonedaEquiv.symm x)).app _ v) = x
  rw [happ, SSet.lastVertex_stdSimplex_vertex]
  simp

/-- Canonical subdivision vertex lifts are natural in the simplicial set. -/
@[simp]
theorem sdVertexOfVertex_naturality {A B : SSet.{u}} (f : A ⟶ B)
    (x : A _⦋0⦌) :
    (SSet.sd.map f).app (op ⦋0⦌) (SSet.sdVertexOfVertex x) =
      SSet.sdVertexOfVertex (f.app (op ⦋0⦌) x) := by
  let v := (SSet.stdSimplex.sdIso.inv.app ⦋0⦌).app (op ⦋0⦌)
    (ComposableArrows.mk₀
      (SimplexCategory.sdSingletonChain ⦋0⦌ 0))
  change ((SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
      SSet.sd.map f).app (op ⦋0⦌)) v =
    (SSet.sd.map
      (SSet.yonedaEquiv.symm (f.app (op ⦋0⦌) x))).app _ v
  rw [← SSet.sd.map_comp, SSet.yonedaEquiv_symm_comp]

end SSet

end
