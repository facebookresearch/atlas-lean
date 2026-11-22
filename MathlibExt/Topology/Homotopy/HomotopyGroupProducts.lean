/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual cube homotopy groups of products

The whole cube map into a product is the family of its actual projected
cube maps. The same holds for homotopies relative to the full boundary.
The quotient comparison is therefore an equivalence in every degree and
a group isomorphism in every positive degree, retaining each projection.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w
open scoped unitInterval Topology Topology.Homotopy

namespace GenLoop.ProductGeometry

variable {ι : Type u} {N : Type w} {X : ι → Type v}
  [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)

/-- Every whole original cube map retains its actual coordinate cube maps. -/
def coordinate (p : GenLoop N (∀ i, X i) x) (i : ι) : GenLoop N (X i) (x i) :=
  GenLoop.map (ContinuousMap.eval i) p

/-- The actual whole product cube map is constructed from all original coordinate maps. -/
def assemble (p : ∀ i, GenLoop N (X i) (x i)) : GenLoop N (∀ i, X i) x :=
  ⟨ContinuousMap.pi (fun i => (p i).val), by
    intro t ht
    funext i
    exact (p i).property t ht⟩

/-- The complete coordinate cube map survives assembly literally. -/
theorem coordinate_assemble (p : ∀ i, GenLoop N (X i) (x i)) (i : ι) :
    coordinate x (assemble x p) i = p i := by
  ext t
  rfl

/-- All actual coordinate cube maps jointly determine the original whole cube map. -/
theorem assemble_coordinate (p : GenLoop N (∀ i, X i) x) :
    assemble x (coordinate x p) = p := by
  ext t i
  rfl

/-- Homotopies of all original projected cubes assemble into a whole boundary-fixed homotopy. -/
theorem homotopic_of_coordinates {p q : GenLoop N (∀ i, X i) x}
    (h : ∀ i, GenLoop.Homotopic (coordinate x p i) (coordinate x q i)) :
    GenLoop.Homotopic p q := by
  let H (i : ι) := Classical.choice (h i)
  let e : ContinuousMap.HomotopyRel
      (ContinuousMap.pi (fun i => (coordinate x p i).val))
      (ContinuousMap.pi (fun i => (coordinate x q i).val)) (Cube.boundary N) := {
    toHomotopy := ContinuousMap.Homotopy.pi (fun i => (H i).toHomotopy)
    prop' := by
      intro t z hz
      funext i
      exact (H i).prop t z hz }
  have hp : ContinuousMap.pi (fun i => (coordinate x p i).val) = p.val := by
    ext t i
    rfl
  have hq : ContinuousMap.pi (fun i => (coordinate x q i).val) = q.val := by
    ext t i
    rfl
  exact ⟨e.cast hp hq⟩

end GenLoop.ProductGeometry

namespace HomotopyGroup.ProductGeometry

variable {ι : Type u} {N : Type w} {X : ι → Type v}
  [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)

/-- The original quotient comparison is the family of the actual continuous projection maps. -/
def comparison (a : HomotopyGroup N (∀ i, X i) x) : ∀ i, HomotopyGroup N (X i) (x i) :=
  fun i => HomotopyGroup.map (ContinuousMap.eval i) a

/-- Every whole original cube representative projects to the same original coordinate representatives. -/
theorem comparison_mk (p : GenLoop N (∀ i, X i) x) (i : ι) :
    comparison x (HomotopyGroup.mk p) i =
      HomotopyGroup.mk (GenLoop.ProductGeometry.coordinate x p i) := rfl

/-- Every original family of homotopy classes is realized by one whole product cube. -/
theorem comparison_surjective : Function.Surjective (comparison (N := N) x) := by
  intro a
  choose p hp using fun i => HomotopyGroup.mk_surjective (a i)
  refine ⟨HomotopyGroup.mk (GenLoop.ProductGeometry.assemble x p), ?_⟩
  funext i
  rw [comparison_mk, GenLoop.ProductGeometry.coordinate_assemble]
  exact hp i

/-- Equality of all actual projected classes detects the original whole boundary-fixed cube class. -/
theorem comparison_injective : Function.Injective (comparison (N := N) x) := by
  intro a b h
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
  apply Quotient.sound
  apply GenLoop.ProductGeometry.homotopic_of_coordinates x
  intro i
  exact Quotient.exact (congrFun h i)

/-- The actual whole product homotopy quotient and all coordinate quotients are equivalent. -/
def equiv : HomotopyGroup N (∀ i, X i) x ≃ ∀ i, HomotopyGroup N (X i) (x i) :=
  Equiv.ofBijective (comparison x) ⟨comparison_injective x, comparison_surjective x⟩

/-- Its full forward coordinate is the original projection map on the original quotient. -/
theorem equiv_coordinate (a : HomotopyGroup N (∀ i, X i) x) (i : ι) :
    equiv x a i = HomotopyGroup.map (ContinuousMap.eval i) a := rfl

/-- Every whole original coordinate map commutes with the product homotopy comparison. -/
theorem comparison_map {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (a : HomotopyGroup N (∀ i, X i) x) (i : ι) :
    comparison (fun i => f i (x i)) (HomotopyGroup.map (ContinuousMap.piMap f) a) i =
      HomotopyGroup.map (f i) (comparison x a i) := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  rw [comparison_mk, HomotopyGroup.map_mk, HomotopyGroup.map_mk]
  apply congrArg HomotopyGroup.mk
  ext t
  rfl

/-- Both inverse and forward product quotient directions retain each supplied original class. -/
theorem equiv_inverse_coordinate (a : ∀ i, HomotopyGroup N (X i) (x i)) (i : ι) :
    HomotopyGroup.map (ContinuousMap.eval i) ((equiv x).symm a) = a i :=
  congrFun ((equiv x).apply_symm_apply a) i

variable [DecidableEq N] [Nonempty N]

/-- The same whole quotient comparison retains the actual positive homotopy multiplication. -/
def hom : HomotopyGroup N (∀ i, X i) x →* ∀ i, HomotopyGroup N (X i) (x i) where
  toFun := comparison x
  map_one' := by funext i; exact HomotopyGroup.map_one _
  map_mul' a b := by funext i; exact HomotopyGroup.map_mul _ a b

/-- The original product quotient equivalence is multiplicative in every positive degree. -/
def mulEquiv : HomotopyGroup N (∀ i, X i) x ≃* ∀ i, HomotopyGroup N (X i) (x i) :=
  MulEquiv.ofBijective (hom x) ⟨comparison_injective x, comparison_surjective x⟩

/-- The full positive comparison uses the identical original coordinate projection functions. -/
theorem mulEquiv_coordinate (a : HomotopyGroup N (∀ i, X i) x) (i : ι) :
    mulEquiv x a i = HomotopyGroup.map (ContinuousMap.eval i) a := rfl

end HomotopyGroup.ProductGeometry

end
end

public section

noncomputable section

universe v

open scoped unitInterval Topology Topology.Homotopy

namespace HomotopyGroup

variable {X : Type v} [TopologicalSpace X]

private def squareFunctionMulEquiv (n : ℕ) (x y : X) :
    Pi (n + 1) (X × X) (x, y) ≃* Pi (n + 1) (Fin 2 → X) (![x, y]) := by
  let e := Homeomorph.finTwoArrow (X := X)
  let f : C(X × X, Fin 2 → X) := ⟨fun p => ![p.1, p.2], by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩
  let g : C(Fin 2 → X, X × X) := ⟨fun p => (p 0, p 1), by fun_prop⟩
  let L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id (X × X)) {(x, y)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (X × X)) {(x, y)}).cast
      (by apply ContinuousMap.ext; intro p; exact (e.apply_symm_apply p).symm) rfl
  let R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id (Fin 2 → X)) {![x, y]} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (Fin 2 → X)) {![x, y]}).cast
      (by apply ContinuousMap.ext; intro p; exact (e.symm_apply_apply p).symm) rfl
  exact mulEquivOfBasedInverse n f g rfl rfl L R

private theorem squareFunctionMulEquiv_apply (n : ℕ) (x y : X)
    (a : Pi (n + 1) (X × X) (x, y)) :
    squareFunctionMulEquiv n x y a =
      HomotopyGroup.map (⟨fun p => ![p.1, p.2], by
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop⟩ : C(X × X, Fin 2 → X)) a := by
  let e := Homeomorph.finTwoArrow (X := X)
  let f : C(X × X, Fin 2 → X) := ⟨e.symm, e.symm.continuous_toFun⟩
  let g : C(Fin 2 → X, X × X) := ⟨e, e.continuous_toFun⟩
  let L : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id (X × X)) {(x, y)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (X × X)) {(x, y)}).cast
      (by apply ContinuousMap.ext; intro p; exact (e.apply_symm_apply p).symm) rfl
  let R : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id (Fin 2 → X)) {![x, y]} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (Fin 2 → X)) {![x, y]}).cast
      (by apply ContinuousMap.ext; intro p; exact (e.symm_apply_apply p).symm) rfl
  exact (mulEquivOfBasedInverse_apply n f g rfl rfl L R a).trans
    (mapHomOfEq_apply f rfl n a)

/-- The actual binary product group comparison in every positive degree,
through the original function-product comparison and the Fin-two homeomorphism. -/
def squareMulEquiv (n : ℕ) (x y : X) :
    Pi (n + 1) (X × X) (x, y) ≃* Pi (n + 1) X x × Pi (n + 1) X y := by
  let T : (∀ i : Fin 2, Pi (n + 1) X ((![x, y] : Fin 2 → X) i)) ≃*
      Pi (n + 1) X x × Pi (n + 1) X y := {
    toEquiv := piFinTwoEquiv (fun i : Fin 2 => Pi (n + 1) X ((![x, y] : Fin 2 → X) i))
    map_mul' := fun _ _ => rfl }
  exact (squareFunctionMulEquiv n x y).trans
    ((ProductGeometry.mulEquiv (N := Fin (n + 1)) (![x, y])).trans T)

/-- The first output is the original first-projection homotopy-group map. -/
theorem squareMulEquiv_fst (n : ℕ) (x y : X)
    (a : Pi (n + 1) (X × X) (x, y)) :
    (squareMulEquiv n x y a).1 =
      HomotopyGroup.map (ContinuousMap.fst : C(X × X, X)) a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  change (ProductGeometry.mulEquiv (N := Fin (n + 1)) (![x, y])
    (squareFunctionMulEquiv n x y (HomotopyGroup.mk p))) 0 = _
  rw [ProductGeometry.mulEquiv_coordinate, squareFunctionMulEquiv_apply]
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, HomotopyGroup.map_mk]
  apply congrArg HomotopyGroup.mk
  ext t
  rfl

/-- The second output is the original second-projection homotopy-group map. -/
theorem squareMulEquiv_snd (n : ℕ) (x y : X)
    (a : Pi (n + 1) (X × X) (x, y)) :
    (squareMulEquiv n x y a).2 =
      HomotopyGroup.map (ContinuousMap.snd : C(X × X, X)) a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  change (ProductGeometry.mulEquiv (N := Fin (n + 1)) (![x, y])
    (squareFunctionMulEquiv n x y (HomotopyGroup.mk p))) 1 = _
  rw [ProductGeometry.mulEquiv_coordinate, squareFunctionMulEquiv_apply]
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, HomotopyGroup.map_mk]
  apply congrArg HomotopyGroup.mk
  ext t
  rfl

/-- The actual inverse class has the supplied original first coordinate. -/
theorem squareMulEquiv_symm_fst (n : ℕ) (x y : X)
    (a : Pi (n + 1) X x) (b : Pi (n + 1) X y) :
    HomotopyGroup.map (ContinuousMap.fst : C(X × X, X)) ((squareMulEquiv n x y).symm (a, b)) = a :=
  (squareMulEquiv_fst n x y _).symm.trans
    (congrArg Prod.fst ((squareMulEquiv n x y).apply_symm_apply (a, b)))

/-- The actual inverse class has the supplied original second coordinate. -/
theorem squareMulEquiv_symm_snd (n : ℕ) (x y : X)
    (a : Pi (n + 1) X x) (b : Pi (n + 1) X y) :
    HomotopyGroup.map (ContinuousMap.snd : C(X × X, X)) ((squareMulEquiv n x y).symm (a, b)) = b :=
  (squareMulEquiv_snd n x y _).symm.trans
    (congrArg Prod.snd ((squareMulEquiv n x y).apply_symm_apply (a, b)))

end HomotopyGroup
