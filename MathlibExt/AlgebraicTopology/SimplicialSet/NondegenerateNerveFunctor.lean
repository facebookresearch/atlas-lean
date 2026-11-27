/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Comparable
public import Mathlib.Order.NonemptyFiniteChains

import Mathlib.Data.Fintype.Powerset

/-!
# Functorial nondegenerate carriers

An arbitrary simplicial map can turn a nondegenerate simplex into a degenerate
one. This file maps it to the unique nondegenerate simplex with the same
generated subcomplex, obtaining a functor to partial orders. For nerves of
partial orders, that partial order is naturally the order of nonempty finite
chains.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet.N

variable {X Y Z : SSet.{u}}

/-- The order hom on nondegenerate simplices induced by a simplicial map. The
image simplex is followed by its unique nondegenerate carrier. -/
noncomputable def map (f : X ⟶ Y) : X.N →o Y.N where
  toFun x := (S.map f x.toS).toN
  monotone' x y h := by
    rw [N.le_iff, S.subcomplex_toN, S.subcomplex_toN]
    change Subcomplex.ofSimplex (f.app _ x.simplex) ≤
      Subcomplex.ofSimplex (f.app _ y.simplex)
    rw [← Subcomplex.image_ofSimplex, ← Subcomplex.image_ofSimplex]
    exact Subcomplex.image_monotone f h

/-- Mapping a nondegenerate carrier maps its generated subcomplex. -/
@[simp]
theorem map_subcomplex (f : X ⟶ Y) (x : X.N) :
    (map f x).subcomplex = x.subcomplex.image f := by
  change (S.map f x.toS).toN.subcomplex = x.subcomplex.image f
  rw [S.subcomplex_toN]
  exact (Subcomplex.image_ofSimplex x.simplex f).symm

/-- The identity map fixes every nondegenerate carrier. -/
@[simp]
theorem map_id_apply (x : X.N) : map (𝟙 X) x = x := by
  apply N.subcomplex_injective
  rw [map_subcomplex, Subcomplex.image_id]

/-- Mapping carriers is compatible with composition. -/
@[simp]
theorem map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.N) :
    map g (map f x) = map (f ≫ g) x := by
  apply N.subcomplex_injective
  rw [map_subcomplex, map_subcomplex, map_subcomplex,
    ← Subcomplex.image_comp]

/-- The functor sending a simplicial set to its ordered type of nondegenerate
carriers. -/
noncomputable def functor : SSet.{u} ⥤ PartOrd.{u} where
  obj X := PartOrd.of X.N
  map f := PartOrd.ofHom (map f)
  map_id X := by
    apply PartOrd.ext
    intro x
    exact map_id_apply x
  map_comp f g := by
    apply PartOrd.ext
    intro x
    exact (map_comp_apply f g x).symm

/-- If the image simplex is nondegenerate, the unique carrier map is the
evident mapped simplex. -/
theorem map_eq_mk (f : X ⟶ Y) (x : X.N)
    (hx : f.app _ x.simplex ∈ Y.nonDegenerate x.dim) :
    map f x = N.mk (f.app _ x.simplex) hx := by
  apply N.subcomplex_injective
  rw [map_subcomplex]
  exact Subcomplex.image_ofSimplex x.simplex f

end SSet.N

namespace PartOrd

open PartialOrder

set_option linter.style.haveILetI false in
/-- Nondegenerate simplices in the nerve of a partial order are naturally its
nonempty finite chains. -/
noncomputable def nerveNOrderIso (P : PartOrd.{u}) :
    (nerve P).N ≃o NonemptyFiniteChains P := by
  classical
  let forward : (nerve P).N → NonemptyFiniteChains P := fun x =>
    { finset := Finset.univ.image x.simplex.obj
      nonempty := by
        refine ⟨x.simplex.obj 0, ?_⟩
        simp
      comparable := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
        obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        rcases le_total i j with hij | hji
        · exact Or.inl (x.simplex.monotone hij)
        · exact Or.inr (x.simplex.monotone hji) }
  have forward_le_iff (x y : (nerve P).N) :
      forward x ≤ forward y ↔ x ≤ y := by
    rw [SSet.N.le_iff,
      PartialOrder.nerve_ofSimplex_le_ofSimplex_iff]
    constructor
    · intro h p hp
      obtain ⟨i, rfl⟩ := hp
      have hi : x.simplex.obj i ∈ (forward x).finset := by
        simp [forward]
      have := h hi
      simpa [forward] using this
    · intro h p hp
      simp only [forward, Finset.mem_image, Finset.mem_univ,
        true_and] at hp ⊢
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨j, hj⟩ := h ⟨i, rfl⟩
      exact ⟨j, hj⟩
  have forward_injective : Function.Injective forward := by
    intro x y h
    apply le_antisymm
    · exact (forward_le_iff x y).mp h.le
    · exact (forward_le_iff y x).mp h.ge
  have exists_backward (A : NonemptyFiniteChains P) :
      ∃ x : (nerve P).N, forward x = A := by
    letI : LinearOrder A.finset :=
      Relation.linearOrderOfSymmGen (fun a b => A.comparable a b)
    let d := A.finset.card - 1
    have hpos : 0 < A.finset.card := Finset.card_pos.mpr A.nonempty
    have hcard : Fintype.card A.finset = d + 1 := by
      dsimp [d]
      rw [Fintype.card_coe]
      omega
    let e : Fin (d + 1) ≃o A.finset :=
      Fintype.orderIsoFinOfCardEq A.finset hcard
    let emb : Fin (d + 1) ↪o P :=
      e.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ A.finset))
    let s : (nerve P) _⦋d⦌ := emb.strictMono.monotone.functor
    have hs : s ∈ (nerve P).nonDegenerate d :=
      PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s |>.2 emb.strictMono
    refine ⟨SSet.N.mk s hs, ?_⟩
    apply NonemptyFiniteChains.ext
    ext p
    constructor
    · intro hp
      simp only [forward, SSet.N.mk_simplex, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (e i).property
    · intro hp
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      simp only [forward, SSet.N.mk_simplex, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact ⟨i, congrArg Subtype.val hi⟩
  let backward : NonemptyFiniteChains P → (nerve P).N := fun A =>
    (exists_backward A).choose
  have right_inv (A : NonemptyFiniteChains P) : forward (backward A) = A :=
    (exists_backward A).choose_spec
  exact
    { toFun := forward
      invFun := backward
      left_inv := fun x => forward_injective (right_inv (forward x))
      right_inv := right_inv
      map_rel_iff' := fun {x y} => forward_le_iff x y }

/-- Membership in the finite chain corresponding to a nondegenerate nerve
simplex is membership in its object range. -/
theorem mem_nerveNOrderIso_finset (P : PartOrd.{u}) (x : (nerve P).N)
    (p : P) :
    p ∈ (nerveNOrderIso P x).finset ↔ ∃ i, x.simplex.obj i = p := by
  classical
  change p ∈ Finset.univ.image x.simplex.obj ↔ _
  simp

/-- The nerve/finite-chain order isomorphism is natural, including for
monotone maps which identify vertices. -/
theorem nerveNOrderIso_naturality {P Q : PartOrd.{u}} (f : P ⟶ Q)
    (x : (nerve P).N) :
    nerveNOrderIso Q
        (SSet.N.map (PartOrd.nerveFunctor.map f) x) =
      NonemptyFiniteChains.map (nerveNOrderIso P x) f.hom := by
  let nf : nerve P ⟶ nerve Q := PartOrd.nerveFunctor.map f
  let y : (nerve Q).N := SSet.N.map nf x
  let t := nf.app _ x.simplex
  have t_obj (j) : t.obj j = f (x.simplex.obj j) := rfl
  have hsub : y.subcomplex = SSet.Subcomplex.ofSimplex t := by
    change (SSet.N.map nf x).subcomplex =
      SSet.Subcomplex.ofSimplex (nf.app _ x.simplex)
    rw [SSet.N.map_subcomplex]
    exact SSet.Subcomplex.image_ofSimplex x.simplex _
  have hrange : Set.range y.simplex.obj = Set.range t.obj := by
    apply Set.Subset.antisymm
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff
          y.simplex t).1 hsub.le
    · exact (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff
          t y.simplex).1 hsub.ge
  apply NonemptyFiniteChains.ext
  ext q
  change q ∈ (nerveNOrderIso Q y).finset ↔
    q ∈ (NonemptyFiniteChains.map (nerveNOrderIso P x) f.hom).finset
  rw [mem_nerveNOrderIso_finset,
    NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hq : q ∈ Set.range y.simplex.obj := ⟨i, hi⟩
    rw [hrange] at hq
    obtain ⟨j, hj⟩ := hq
    refine ⟨x.simplex.obj j, ?_, ?_⟩
    · exact (mem_nerveNOrderIso_finset P x _).2 ⟨j, rfl⟩
    · simpa only [t_obj] using hj
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨j, hj⟩ := (mem_nerveNOrderIso_finset P x p).1 hp
    have hq : q ∈ Set.range t.obj := by
      refine ⟨j, ?_⟩
      rw [t_obj, hj]
      exact hpq
    rw [← hrange] at hq
    exact hq

/-- Naturally, taking nondegenerate carriers in a partial-order nerve is the
same as taking nonempty finite chains. -/
noncomputable def nerveFunctorCompNFunctorIso :
    PartOrd.nerveFunctor ⋙ SSet.N.functor ≅
      PartOrd.nonemptyFiniteChainsFunctor :=
  NatIso.ofComponents
    (fun P => PartOrd.Iso.mk (nerveNOrderIso P))
    (fun f => by
      apply PartOrd.ext
      intro x
      exact nerveNOrderIso_naturality f x)

end PartOrd

namespace SSet

/-- The nerve of the ordered type of nondegenerate simplices. -/
noncomputable def nondegenerateNerve : SSet.{u} ⥤ SSet.{u} :=
  SSet.N.functor ⋙ PartOrd.nerveFunctor

/-- The Barratt nerve of the nondegenerate-carrier poset of a finite
simplicial set is finite. -/
instance finite_nondegenerateNerve (X : SSet.{u}) [X.Finite] :
    (SSet.nondegenerateNerve.obj X).Finite where
  finite := by
    classical
    let _ := Fintype.ofFinite X.N
    let _ : _root_.Finite (PartialOrder.NonemptyFiniteChains X.N) :=
      Finite.of_injective
        (fun A : PartialOrder.NonemptyFiniteChains X.N => A.finset)
        (fun A B h => PartialOrder.NonemptyFiniteChains.ext h)
    change _root_.Finite (CategoryTheory.nerve (PartOrd.of X.N)).N
    exact Finite.of_equiv
      (PartialOrder.NonemptyFiniteChains X.N)
      (PartOrd.nerveNOrderIso (PartOrd.of X.N)).symm.toEquiv

end SSet
