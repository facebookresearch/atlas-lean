/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW

/-!
# Focused clients for the fundamental groupoid of a Kan complex

The test complex is the nerve of the codiscrete category on `Bool`, a Kan complex with two
distinct vertices in which a simplex is determined by its vertices. Its edges and
`2`-simplices are written down explicitly, and composition in the fundamental groupoid is
checked against them: through native Mathlib `SSet.Edge.CompStruct` witnesses, through the
Kan-complex characterisations `homMk_comp_iff` and `homMk_eq_iff_nonempty_homotopyL`, and
through explicit inverses. The weak-equivalence class `KanComplex.W` is exercised on the same
complex.
-/

@[expose] public section

namespace KanComplexFundamentalGroupoidTests

open CategoryTheory Simplicial SSet

/-- The nerve of the codiscrete category on `Bool`. -/
abbrev B : SSet.{0} := nerve (Codiscrete Bool)

instance : KanComplex B := Codiscrete.nerve_codiscrete_kanComplex Bool

/-- The vertex of `B` at `b`. -/
noncomputable def v (b : Bool) : B _⦋0⦌ := Codiscrete.equivFun.symm fun _ ↦ b

/-- The edge of `B` from `a` to `b`. -/
noncomputable def e (a b : Bool) : Edge (v a) (v b) :=
  Edge.mk (Codiscrete.equivFun.symm ![a, b])
    (Codiscrete.equivFun.injective (funext fun k ↦ by fin_cases k; rfl))
    (Codiscrete.equivFun.injective (funext fun k ↦ by fin_cases k; rfl))

/-- The `2`-simplex of `B` with vertices `a`, `b`, `c`, as a composition witness. -/
noncomputable def t (a b c : Bool) : Edge.CompStruct (e a b) (e b c) (e a c) :=
  Edge.CompStruct.mk (Codiscrete.equivFun.symm ![a, b, c])
    (Codiscrete.equivFun.injective (funext fun k ↦ by fin_cases k <;> rfl))
    (Codiscrete.equivFun.injective (funext fun k ↦ by fin_cases k <;> rfl))
    (Codiscrete.equivFun.injective (funext fun k ↦ by fin_cases k <;> rfl))

/-- The two vertices are distinct, so the clients below are not about a point. -/
theorem v_false_ne_v_true : v false ≠ v true := by
  intro h
  have := congrFun (congrArg Codiscrete.equivFun h) 0
  simp [v] at this

/-- An edge of `B` is determined by its endpoints. -/
theorem edge_eq_e {a b : Bool} (f : Edge (v a) (v b)) : f = e a b := by
  apply Edge.ext
  apply Codiscrete.equivFun.injective
  funext k
  fin_cases k
  · exact congrFun (congrArg Codiscrete.equivFun f.src_eq) 0
  · exact congrFun (congrArg Codiscrete.equivFun f.tgt_eq) 0

/-- The constant edge is the identity edge. -/
theorem e_self (a : Bool) : e a a = Edge.id (v a) :=
  (edge_eq_e (Edge.id (v a))).symm

/-- Composition of explicit edges in the fundamental groupoid. -/
theorem homMk_e_comp (a b c : Bool) :
    FundamentalGroupoid.homMk (e a b) ≫ FundamentalGroupoid.homMk (e b c) =
      FundamentalGroupoid.homMk (e a c) :=
  (t a b c).homMk_comp

/-- The native Mathlib composite of two explicit edges is the explicit edge. -/
theorem comp_e (a b c : Bool) : Edge.comp (e a b) (e b c) = e a c :=
  edge_eq_e _

/-- A round trip between the two distinct vertices is the identity. -/
theorem homMk_round_trip :
    FundamentalGroupoid.homMk (e false true) ≫ FundamentalGroupoid.homMk (e true false) =
      𝟙 (FundamentalGroupoid.mk (v false)) := by
  rw [homMk_e_comp, e_self, FundamentalGroupoid.homMk_id]

/-- The Kan-complex criterion recovers a composition witness from the round trip. -/
theorem nonempty_compStruct_round_trip :
    Nonempty (Edge.CompStruct (e false true) (e true false) (Edge.id (v false))) := by
  rw [← FundamentalGroupoid.homMk_comp_iff, FundamentalGroupoid.homMk_id]
  exact homMk_round_trip

/-- The chosen inverse of an explicit edge is the reversed edge. -/
theorem inv_e (a b : Bool) : (e a b).inv = e b a :=
  edge_eq_e _

/-- `homMk_inv` on an explicit edge between distinct vertices. -/
theorem inv_homMk_e :
    inv (FundamentalGroupoid.homMk (e false true)) = FundamentalGroupoid.homMk (e true false) := by
  rw [← FundamentalGroupoid.homMk_inv, inv_e]

/-- Two edges with the same endpoints give equal morphisms, witnessed by a left homotopy. -/
theorem nonempty_homotopyL (a b : Bool) :
    Nonempty (Edge.HomotopyL (Edge.comp (e a b) (e b b)) (e a b)) := by
  rw [← FundamentalGroupoid.homMk_eq_iff_nonempty_homotopyL, comp_e]

/-- Every morphism of the fundamental groupoid of `B` comes from the explicit edge. -/
theorem hom_eq_homMk_e {a b : Bool}
    (f : FundamentalGroupoid.mk (v a) ⟶ FundamentalGroupoid.mk (v b)) :
    f = FundamentalGroupoid.homMk (e a b) := by
  induction f using FundamentalGroupoid.hom_rec_of_kanComplex with
  | homMk f => rw [edge_eq_e f]

/-- The isomorphism with the `2`-truncated homotopy category sends an explicit edge to its
class. -/
example (a b : Bool) :
    (KanComplex.isoCatFundamentalGroupoid B).functor.map
        (Truncated.HomotopyCategory₂.homMk (e a b).toTruncated) =
      FundamentalGroupoid.homMk (e a b) :=
  KanComplex.isoCatFundamentalGroupoid_functor_map_homMk (e a b)

/-- The identity of the Kan complex `B` is a weak equivalence. -/
example : KanComplex.W (𝟙 B) := KanComplex.W.id

/-- The automorphism of `B` induced by swapping the two elements of `Bool`. -/
noncomputable def swapIso : B ≅ B :=
  Codiscrete.functorToSSet.mapIso (Equiv.swap false true).toIso

/-- The swap moves the vertex `false` to the distinct vertex `true`. -/
theorem swapIso_hom_v_false : swapIso.hom.app _ (v false) = v true := by
  apply Codiscrete.equivFun.injective
  funext k
  rfl

/-- So the swap is a weak equivalence that is not the identity. -/
example : KanComplex.W swapIso.hom ∧ swapIso.hom ≠ 𝟙 B :=
  ⟨KanComplex.W.ofIso swapIso, fun h ↦ v_false_ne_v_true (by
    simpa [h] using swapIso_hom_v_false)⟩

/-- A weak equivalence induces an equivalence of fundamental groupoids. -/
example : (mapFundamentalGroupoid (𝟙 B)).IsEquivalence :=
  (KanComplex.W.id (X := B)).isEquivalence_mapFundamentalGroupoid

end KanComplexFundamentalGroupoidTests
