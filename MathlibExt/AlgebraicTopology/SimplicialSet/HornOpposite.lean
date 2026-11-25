/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Opposite horns and lifting squares

The opposite of the `i`-th horn is the `i.rev`-th horn.  This file lifts
Mathlib's subcomplex equation to simplicial-set and Arrow isomorphisms, then
packages equivalences of horn squares and their diagonal fillers.  It also
records the small double-op identities needed to transport fillers back.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

namespace Subcomplex

variable {X Y : SSet.{u}} (e : Y ≅ X) (A : X.Subcomplex)

/-- Forward map of `Subcomplex.preimageIso`. -/
private def preimageIsoHom :
    (A : SSet.{u}) ⟶ ((A.preimage e.hom : Y.Subcomplex) : SSet.{u}) :=
  Subcomplex.lift (A.ι ≫ e.inv) (by
    intro d x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨a, rfl⟩ := hx
    change e.hom.app d ((A.ι ≫ e.inv).app d a) ∈ A.obj d
    rw [show (A.ι ≫ e.inv).app d a = e.inv.app d a.val from rfl]
    have h3 : (e.inv ≫ e.hom).app d a.val = a.val := by
      rw [e.inv_hom_id]
      rfl
    have h2 : e.hom.app d (e.inv.app d a.val) = a.val := h3
    rw [h2]
    exact a.2)

/-- Backward map of `Subcomplex.preimageIso`. -/
private def preimageIsoInv :
    ((A.preimage e.hom : Y.Subcomplex) : SSet.{u}) ⟶ (A : SSet.{u}) :=
  Subcomplex.lift ((A.preimage e.hom).ι ≫ e.hom) (by
    intro d x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨b, rfl⟩ := hx
    change ((A.preimage e.hom).ι ≫ e.hom).app d b ∈ A.obj d
    rw [show ((A.preimage e.hom).ι ≫ e.hom).app d b =
      e.hom.app d b.val from rfl]
    exact b.2)

@[reassoc]
private lemma preimageIsoHom_ι :
    preimageIsoHom e A ≫ (A.preimage e.hom).ι = A.ι ≫ e.inv :=
  Subcomplex.lift_ι _ _

@[reassoc]
private lemma preimageIsoInv_ι :
    preimageIsoInv e A ≫ A.ι = (A.preimage e.hom).ι ≫ e.hom :=
  Subcomplex.lift_ι _ _

/-- The preimage of a subcomplex along an isomorphism is isomorphic
to the original subcomplex. -/
private def preimageIso :
    (A : SSet.{u}) ≅ ((A.preimage e.hom : Y.Subcomplex) : SSet.{u}) where
  hom := preimageIsoHom e A
  inv := preimageIsoInv e A
  hom_inv_id := by
    ext d x
    refine Subtype.ext ?_
    change ((preimageIsoHom e A ≫ preimageIsoInv e A).app d x).val = x.val
    change e.hom.app d (e.inv.app d x.val) = x.val
    have h3 : (e.inv ≫ e.hom).app d x.val = x.val := by
      rw [e.inv_hom_id]
      rfl
    exact h3
  inv_hom_id := by
    ext d x
    refine Subtype.ext ?_
    change ((preimageIsoInv e A ≫ preimageIsoHom e A).app d x).val = x.val
    change e.inv.app d (e.hom.app d x.val) = x.val
    have h3 : (e.hom ≫ e.inv).app d x.val = x.val := by
      rw [e.hom_inv_id]
      rfl
    exact h3

end Subcomplex

section HornOppositeIso

/-- The opposite of the `i`-th horn is the `i.rev`-th horn. The
subcomplex-level equation is Mathlib's `SSet.op_horn`; the opposite
subcomplex coerced to `SSet` is definitionally the opposite of the
coerced subcomplex, so only the preimage-along-iso step is new. -/
@[no_expose]
def hornOppositeIso (n : ℕ) (i : Fin (n + 1)) :
    ((Λ[n, i] : SSet.{u}).op) ≅ (Λ[n, i.rev] : SSet.{u}) :=
  Subcomplex.preimageIso (stdSimplex.opIso ⦋n⦌).symm Λ[n, i].op ≪≫
    Subcomplex.eqToIso (SSet.op_horn i)

/-- Naturality of `hornOppositeIso` with the horn inclusions: the
opposite inclusion corresponds to the reversed inclusion through
`stdSimplex.opIso`. -/
lemma hornOppositeIso_hom_ι (n : ℕ) (i : Fin (n + 1)) :
    (hornOppositeIso n i).hom ≫ Λ[n, i.rev].ι =
      opFunctor.map Λ[n, i].ι ≫ (stdSimplex.opIso ⦋n⦌).hom := by
  have h1 : (Subcomplex.eqToIso (SSet.op_horn i)).hom ≫ Λ[n, i.rev].ι =
      (Λ[n, i].op.preimage (stdSimplex.opIso ⦋n⦌).symm.hom).ι :=
    Subcomplex.homOfLE_ι (SSet.op_horn i).le
  have key : Subcomplex.preimageIsoHom (stdSimplex.opIso ⦋n⦌).symm
          Λ[n, i].op ≫ (Subcomplex.eqToIso (SSet.op_horn i)).hom ≫
          Λ[n, i.rev].ι =
        opFunctor.map Λ[n, i].ι ≫ (stdSimplex.opIso ⦋n⦌).hom := by
    rw [h1, Subcomplex.preimageIsoHom_ι]
    rfl
  exact key

end HornOppositeIso

section OpToolkit

/-- `opFunctor.map` is injective: it is the functor part of the
op-equivalence. -/
private lemma opFunctor_map_injective {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : opFunctor.map f = opFunctor.map g) : f = g :=
  SSet.opEquivalence.functor.map_injective h

/-- The unit of the op-equivalence, in `opFunctor` form. Stated with
`opFunctor` (rather than the `⋙`-form of `opEquivalence`) so that
rewriting never crosses a definitional boundary. -/
private def opUnit (X : SSet.{u}) : X ⟶ X.op.op :=
  (SSet.opEquivalence.unitIso.app X).hom

/-- The counit of the op-equivalence, in `opFunctor` form. -/
private def opCounit (X : SSet.{u}) : X.op.op ⟶ X :=
  (SSet.opEquivalence.counitIso.app X).hom

/-- Applying `stdSimplex.opObjEquiv.symm` twice is the identity, seen
on vertices: each application reverses the index and the value. -/
private lemma opObjEquiv_symm_symm_apply {n d : ℕ} (x : Δ[n] _⦋d⦌)
    (i : Fin (d + 1)) :
    (show Δ[n] _⦋d⦌ from
      stdSimplex.opObjEquiv.{u, u}.symm (stdSimplex.opObjEquiv.{u, u}.symm x)) i = x i := by
  have h1 := stdSimplex.opObjEquiv_opObjEquiv_symm_apply
    (show Δ[n] _⦋d⦌ from stdSimplex.opObjEquiv.{u, u}.symm x) i
  have h2 := stdSimplex.opObjEquiv_opObjEquiv_symm_apply x i.rev
  have e1 : (show Δ[n] _⦋d⦌ from stdSimplex.opObjEquiv.{u, u}.symm
      (stdSimplex.opObjEquiv.{u, u}.symm x)) =
      opObjEquiv (stdSimplex.opObjEquiv.{u, u}.symm
        (show Δ[n] _⦋d⦌ from stdSimplex.opObjEquiv.{u, u}.symm x)) := rfl
  have e2 : (show Δ[n] _⦋d⦌ from
      stdSimplex.opObjEquiv.{u, u}.symm x) =
      opObjEquiv (stdSimplex.opObjEquiv.{u, u}.symm x) := rfl
  rw [e1, h1, e2, h2, Fin.rev_rev, Fin.rev_rev]

/-- The composite `opIso.inv ≫ op(opIso.inv)` is the unit of the
op-equivalence: both sides act as the identity on simplices. -/
private lemma opIso_inv_map_opIso_inv (n : ℕ) :
    (stdSimplex.opIso.{u} ⦋n⦌).inv ≫
        opFunctor.map (stdSimplex.opIso.{u} ⦋n⦌).inv =
      SSet.opUnit Δ[n] := by
  ext d x
  match d with
  | op ⟨k⟩ =>
    change ((stdSimplex.opIso.{u} ⦋n⦌).inv ≫ opFunctor.map
          (stdSimplex.opIso.{u} ⦋n⦌).inv).app _ x =
        (SSet.opUnit Δ[n]).app _ x
    have hLHS : ((stdSimplex.opIso.{u} ⦋n⦌).inv ≫ opFunctor.map
          (stdSimplex.opIso.{u} ⦋n⦌).inv).app _ x =
        (show Δ[n] _⦋k⦌ from stdSimplex.opObjEquiv.{u, u}.symm
          (stdSimplex.opObjEquiv.{u, u}.symm x)) := rfl
    have hRHS : (SSet.opUnit Δ[n]).app _ x = x := rfl
    rw [hLHS, hRHS]
    exact stdSimplex.ext _ _ (fun i ↦ opObjEquiv_symm_symm_apply x i)

end OpToolkit

end SSet
namespace SSet

/-- Turn an `n`-simplex of an opposite simplicial set back into an
`n`-simplex of the original simplicial set. -/
private noncomputable def unopSimplexMap {X : SSet.{u}} (n : ℕ)
    (σ : Δ[n] ⟶ X.op) : Δ[n] ⟶ X :=
  (stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ ≫ opCounit X

/-- Opposing `unopSimplexMap` recovers the original opposite simplex. -/
private lemma unopSimplexMap_op {X : SSet.{u}} (n : ℕ) (σ : Δ[n] ⟶ X.op) :
    (stdSimplex.opIso ⦋n⦌).inv ≫
      opFunctor.map (unopSimplexMap n σ) = σ := by
  change (stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map
      ((stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ ≫ opCounit X) = σ
  have nat : opUnit Δ[n] ≫ opFunctor.map (opFunctor.map σ) =
      σ ≫ opUnit X.op :=
    opEquivalence.unitIso.hom.naturality σ
  have tri : opUnit X.op ≫ opFunctor.map (opCounit X) = 𝟙 X.op :=
    opEquivalence.toAdjunction.right_triangle_components X
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    opIso_inv_map_opIso_inv, ← Category.assoc, nat, Category.assoc,
    tri, Category.comp_id]

end SSet

namespace SSet.horn

/-- Opposite transport identifies a horn inclusion with the reversed horn
inclusion as an object of the arrow category. -/
noncomputable def opArrowIso (n : ℕ) (i : Fin (n + 1)) :
    SSet.opFunctor.mapArrow.obj (Arrow.mk (SSet.horn.{u} n i).ι) ≅
      Arrow.mk (SSet.horn.{u} n i.rev).ι :=
  Arrow.isoMk (SSet.hornOppositeIso n i) (SSet.stdSimplex.opIso ⦋n⦌)
    (SSet.hornOppositeIso_hom_ι n i)

@[reassoc]
lemma opArrowIso_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (SSet.hornOppositeIso.{u} n i).inv ≫
        SSet.opFunctor.map (SSet.horn n i).ι =
      (SSet.horn n i.rev).ι ≫
        (SSet.stdSimplex.opIso ⦋n⦌).inv := by
  exact (opArrowIso.{u} n i).inv.w

/-- Opposite transport gives an equivalence between a horn square and its
index-reversed opposite square. -/
noncomputable def opArrowHomEquiv {X Y : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y) :
    (Arrow.mk (SSet.horn.{u} n i).ι ⟶ Arrow.mk p) ≃
      (Arrow.mk (SSet.horn.{u} n i.rev).ι ⟶
        Arrow.mk (SSet.opFunctor.map p)) :=
  ((Functor.mapArrowEquivalence
      SSet.opEquivalence).fullyFaithfulFunctor.homEquiv).trans
    (Iso.homCongr (opArrowIso n i) (Iso.refl _))

@[simp]
lemma opArrowHomEquiv_apply_left {X Y : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y)
    (sq : Arrow.mk (SSet.horn.{u} n i).ι ⟶ Arrow.mk p) :
    (opArrowHomEquiv n i p sq).left =
      (SSet.hornOppositeIso n i).inv ≫ SSet.opFunctor.map sq.left := by
  rfl

@[simp]
lemma opArrowHomEquiv_apply_right {X Y : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y)
    (sq : Arrow.mk (SSet.horn.{u} n i).ι ⟶ Arrow.mk p) :
    (opArrowHomEquiv n i p sq).right =
      (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
        SSet.opFunctor.map sq.right := by
  rfl

/-- Opposite transport identifies diagonal fillers of a horn square with
diagonal fillers of its index-reversed opposite square. -/
noncomputable def opLiftStructEquiv {X Y : SSet.{u}}
    {n : ℕ} {i : Fin (n + 1)} {p : X ⟶ Y}
    (sq : Arrow.mk (SSet.horn.{u} n i).ι ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (opArrowHomEquiv n i p sq) where
  toFun l :=
    { l := (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
        SSet.opFunctor.map l.l
      fac_left := by
        have hfl : (SSet.horn n i).ι ≫ l.l = sq.left := l.fac_left
        calc
          (SSet.horn n i.rev).ι ≫
              ((SSet.stdSimplex.opIso ⦋n⦌).inv ≫
                SSet.opFunctor.map l.l) =
            ((SSet.horn n i.rev).ι ≫
              (SSet.stdSimplex.opIso ⦋n⦌).inv) ≫
                SSet.opFunctor.map l.l := (Category.assoc _ _ _).symm
          _ = ((SSet.hornOppositeIso n i).inv ≫
              SSet.opFunctor.map (SSet.horn n i).ι) ≫
                SSet.opFunctor.map l.l := by rw [opArrowIso_inv_ι]
          _ = (SSet.hornOppositeIso n i).inv ≫
              (SSet.opFunctor.map (SSet.horn n i).ι ≫
                SSet.opFunctor.map l.l) := Category.assoc _ _ _
          _ = (SSet.hornOppositeIso n i).inv ≫
              SSet.opFunctor.map ((SSet.horn n i).ι ≫ l.l) := by
                rw [Functor.map_comp]
          _ = (SSet.hornOppositeIso n i).inv ≫
              SSet.opFunctor.map sq.left := by rw [hfl]
          _ = (opArrowHomEquiv n i p sq).left := by
                rw [opArrowHomEquiv_apply_left]
      fac_right := by
        have hfr : l.l ≫ p = sq.right := l.fac_right
        calc
          ((SSet.stdSimplex.opIso ⦋n⦌).inv ≫
              SSet.opFunctor.map l.l) ≫ SSet.opFunctor.map p =
            (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
              (SSet.opFunctor.map l.l ≫ SSet.opFunctor.map p) :=
                Category.assoc _ _ _
          _ = (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
              SSet.opFunctor.map (l.l ≫ p) := by rw [Functor.map_comp]
          _ = (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
              SSet.opFunctor.map sq.right := by rw [hfr]
          _ = (opArrowHomEquiv n i p sq).right := by
                rw [opArrowHomEquiv_apply_right] }
  invFun l :=
    { l := (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
        SSet.opFunctor.map l.l ≫ (SSet.opEquivalence.counitIso.app X).hom
      fac_left := by
        apply SSet.opFunctor_map_injective
        have hfl : (SSet.horn n i.rev).ι ≫ l.l =
            (opArrowHomEquiv n i p sq).left := l.fac_left
        calc
          SSet.opFunctor.map ((SSet.horn n i).ι ≫
              SSet.unopSimplexMap n l.l) =
            SSet.opFunctor.map (SSet.horn n i).ι ≫
              SSet.opFunctor.map (SSet.unopSimplexMap n l.l) :=
                Functor.map_comp _ _ _
          _ = SSet.opFunctor.map sq.left := by
            apply (cancel_epi (SSet.hornOppositeIso n i).inv).mp
            calc
              (SSet.hornOppositeIso n i).inv ≫
                  (SSet.opFunctor.map (SSet.horn n i).ι ≫
                    SSet.opFunctor.map (SSet.unopSimplexMap n l.l)) =
                ((SSet.horn n i.rev).ι ≫
                  (SSet.stdSimplex.opIso ⦋n⦌).inv) ≫
                    SSet.opFunctor.map (SSet.unopSimplexMap n l.l) := by
                      rw [← Category.assoc, opArrowIso_inv_ι]
              _ = (SSet.horn n i.rev).ι ≫ l.l := by
                    rw [Category.assoc, SSet.unopSimplexMap_op]
              _ = (opArrowHomEquiv n i p sq).left := hfl
              _ = (SSet.hornOppositeIso n i).inv ≫
                    SSet.opFunctor.map sq.left := by
                      rw [opArrowHomEquiv_apply_left]
      fac_right := by
        apply SSet.opFunctor_map_injective
        have hfr : l.l ≫ SSet.opFunctor.map p =
            (opArrowHomEquiv n i p sq).right := l.fac_right
        calc
          SSet.opFunctor.map (SSet.unopSimplexMap n l.l ≫ p) =
              SSet.opFunctor.map (SSet.unopSimplexMap n l.l) ≫
                SSet.opFunctor.map p := Functor.map_comp _ _ _
          _ = SSet.opFunctor.map sq.right := by
            apply (cancel_epi (SSet.stdSimplex.opIso ⦋n⦌).inv).mp
            calc
              (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
                  (SSet.opFunctor.map (SSet.unopSimplexMap n l.l) ≫
                    SSet.opFunctor.map p) =
                l.l ≫ SSet.opFunctor.map p := by
                  rw [← Category.assoc, SSet.unopSimplexMap_op]
              _ = (opArrowHomEquiv n i p sq).right := hfr
              _ = (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
                    SSet.opFunctor.map sq.right := by
                      rw [opArrowHomEquiv_apply_right] }
  left_inv l := by
    apply CommSq.LiftStruct.ext
    change SSet.unopSimplexMap n
      ((SSet.stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map l.l) = l.l
    apply SSet.opFunctor_map_injective
    apply (cancel_epi (SSet.stdSimplex.opIso ⦋n⦌).inv).mp
    rw [SSet.unopSimplexMap_op]
  right_inv l := by
    apply CommSq.LiftStruct.ext
    change (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
      SSet.opFunctor.map (SSet.unopSimplexMap n l.l) = l.l
    exact SSet.unopSimplexMap_op n l.l

@[simp]
lemma opLiftStructEquiv_apply_l {X Y : SSet.{u}}
    {n : ℕ} {i : Fin (n + 1)} {p : X ⟶ Y}
    (sq : Arrow.mk (SSet.horn.{u} n i).ι ⟶ Arrow.mk p)
    (l : Arrow.LiftStruct sq) :
    (opLiftStructEquiv sq l).l =
      (SSet.stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map l.l :=
  rfl

end SSet.horn
