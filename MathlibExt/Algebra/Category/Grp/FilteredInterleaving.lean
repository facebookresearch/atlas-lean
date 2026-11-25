/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Interleaved sequences of groups

For two sequences `D` and `E`, maps `a n : D n ⟶ E n` and
`b n : E n ⟶ D (n + 1)` give an isomorphism of their original filtered
group colimits when both successive composites are the original transition
maps. Naturality follows from those two equations. The forward map uses
`IsColimit.map` between the chosen group quotient cocones. The inverse sends
leg `n` of `E` through `b n` to leg `n + 1` of `D`.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open GrpCat.FilteredColimits
open GrpCat.FilteredColimits.Successor

namespace GrpCat.FilteredInterleaving

local notation "qfac" => (fun α j =>
  IsColimit.ι_map (colimitCoconeIsColimit _) (colimitCocone _) α j)

/-- The original adjacent transition of a sequence of groups. -/
def step (D : ℕ ⥤ GrpCat.{u}) (n : ℕ) : D.obj n ⟶ D.obj (n + 1) :=
  D.map (homOfLE (Nat.le_succ n))

variable (D E : ℕ ⥤ GrpCat.{u})
  (a : ∀ n, D.obj n ⟶ E.obj n) (b : ∀ n, E.obj n ⟶ D.obj (n + 1))
  (ha : ∀ n, a n ≫ b n = step D n)
  (hb : ∀ n, b n ≫ a (n + 1) = step E n)

include ha hb

/-- The two interleaving equations imply every adjacent square for `a`. -/
theorem a_succ_naturality (n : ℕ) :
    step D n ≫ a (n + 1) = a n ≫ step E n := by
  rw [← ha n, Category.assoc, hb n]

/-- The two interleaving equations imply every adjacent square for `b`. -/
theorem b_succ_naturality (n : ℕ) :
    step E n ≫ b (n + 1) = b n ≫ step D (n + 1) := by
  rw [← hb n, Category.assoc, ha (n + 1)]

/-- The actual stage maps `a` form a natural transformation on all of `ℕ`. -/
def aNatTrans : D ⟶ E :=
  NatTrans.ofSequence a (a_succ_naturality D E a b ha hb)

/-- The actual stage maps `b` form a transformation into the successor diagram. -/
def bNatTrans : E ⟶ successorFunctor ⋙ D :=
  NatTrans.ofSequence b (fun n => by
    change step E n ≫ b (n + 1) = b n ≫ step D (n + 1)
    exact b_succ_naturality D E a b ha hb n)

@[simp]
theorem aNatTrans_app (n : ℕ) : (aNatTrans D E a b ha hb).app n = a n := rfl

@[simp]
theorem bNatTrans_app (n : ℕ) : (bNatTrans D E a b ha hb).app n = b n := rfl

/-- Naturality of `a` holds for each original finite index map. -/
theorem a_naturality {i j : ℕ} (f : i ⟶ j) :
    D.map f ≫ a j = a i ≫ E.map f :=
  (aNatTrans D E a b ha hb).naturality f

/-- Naturality of `b` holds for each original finite index map. -/
theorem b_naturality {i j : ℕ} (f : i ⟶ j) :
    E.map f ≫ b j = b i ≫ D.map (successorFunctor.map f) :=
  (bNatTrans D E a b ha hb).naturality f

/-- The first interleaving equation holds as a whole natural transformation. -/
theorem aNatTrans_comp_bNatTrans :
    aNatTrans D E a b ha hb ≫ bNatTrans D E a b ha hb =
      successorTransitionNatTrans.app D := by
  apply NatTrans.ext
  funext n
  exact (ha n).trans (successorTransitionNatTrans_app_app D n).symm

/-- The second interleaving equation holds as a whole natural transformation. -/
theorem bNatTrans_comp_whisker_aNatTrans :
    bNatTrans D E a b ha hb ≫ Functor.whiskerLeft successorFunctor
      (aNatTrans D E a b ha hb) = successorTransitionNatTrans.app E := by
  apply NatTrans.ext
  funext n
  exact (hb n).trans (successorTransitionNatTrans_app_app E n).symm

/-- The inverse cocone has the original `D` quotient as its point. -/
def inverseCocone : Cocone E where
  pt := GrpCat.FilteredColimits.colimit D
  ι := bNatTrans D E a b ha hb ≫ (successorCocone D).ι

@[simp]
theorem inverseCocone_ι (n : ℕ) :
    (inverseCocone D E a b ha hb).ι.app n =
      b n ≫ (colimitCocone D).ι.app (n + 1) := rfl

/-- The inverse is induced by the actual original `E` colimit universal property. -/
def inverse : GrpCat.FilteredColimits.colimit E ⟶ GrpCat.FilteredColimits.colimit D :=
  (colimitCoconeIsColimit E).desc (inverseCocone D E a b ha hb)

/-- Every original `E` leg is sent to the original successor `D` leg through `b`. -/
@[simp]
theorem inverse_ι (n : ℕ) :
    (colimitCocone E).ι.app n ≫ inverse D E a b ha hb =
      b n ≫ (colimitCocone D).ι.app (n + 1) :=
  (colimitCoconeIsColimit E).fac (inverseCocone D E a b ha hb) n

/-- The forward colimit map followed by the legwise inverse is the identity. -/
theorem forward_inverse :
    natQuotientColimit.map (aNatTrans D E a b ha hb) ≫ inverse D E a b ha hb =
      𝟙 (GrpCat.FilteredColimits.colimit D) := by
  apply (colimitCoconeIsColimit D).hom_ext
  intro n
  have hf := qfac (aNatTrans D E a b ha hb) n
  have hi := inverse_ι D E a b ha hb n
  have hw := (colimitCocone D).w (homOfLE (Nat.le_succ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ inverse D E a b ha hb) hf).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a n ≫ f) hi).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ (colimitCocone D).ι.app (n + 1)) (ha n)).trans
              (hw.trans (Category.comp_id _).symm))))))

/-- The legwise inverse followed by the forward colimit map is the identity. -/
theorem inverse_forward :
    inverse D E a b ha hb ≫ natQuotientColimit.map (aNatTrans D E a b ha hb) =
      𝟙 (GrpCat.FilteredColimits.colimit E) := by
  apply (colimitCoconeIsColimit E).hom_ext
  intro n
  have hi := inverse_ι D E a b ha hb n
  have hf := qfac (aNatTrans D E a b ha hb) (n + 1)
  have hw := (colimitCocone E).w (homOfLE (Nat.le_succ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ natQuotientColimit.map (aNatTrans D E a b ha hb)) hi).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => b n ≫ f) hf).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ (colimitCocone E).ι.app (n + 1)) (hb n)).trans
              (hw.trans (Category.comp_id _).symm))))))

/-- Interleaving alone gives an isomorphism of the two original group colimits. -/
def colimitIso : GrpCat.FilteredColimits.colimit D ≅ GrpCat.FilteredColimits.colimit E where
  hom := natQuotientColimit.map (aNatTrans D E a b ha hb)
  inv := inverse D E a b ha hb
  hom_inv_id := forward_inverse D E a b ha hb
  inv_hom_id := inverse_forward D E a b ha hb

@[simp]
theorem colimitIso_hom :
    (colimitIso D E a b ha hb).hom = natQuotientColimit.map (aNatTrans D E a b ha hb) := rfl

@[simp]
theorem colimitIso_inv :
    (colimitIso D E a b ha hb).inv = inverse D E a b ha hb := rfl

/-- The forward isomorphism retains every actual original stage map and leg. -/
theorem colimitIso_hom_ι (n : ℕ) :
    (colimitCocone D).ι.app n ≫ (colimitIso D E a b ha hb).hom =
      a n ≫ (colimitCocone E).ι.app n :=
  qfac (aNatTrans D E a b ha hb) n

/-- The inverse isomorphism retains every actual original successor leg. -/
theorem colimitIso_inv_ι (n : ℕ) :
    (colimitCocone E).ι.app n ≫ (colimitIso D E a b ha hb).inv =
      b n ≫ (colimitCocone D).ι.app (n + 1) :=
  inverse_ι D E a b ha hb n

theorem colimitIso_hom_ι_apply (n : ℕ) (x : D.obj n) :
    (colimitIso D E a b ha hb).hom ((colimitCocone D).ι.app n x) =
      (colimitCocone E).ι.app n (a n x) :=
  ConcreteCategory.congr_hom (colimitIso_hom_ι D E a b ha hb n) x

theorem colimitIso_inv_ι_apply (n : ℕ) (x : E.obj n) :
    (colimitIso D E a b ha hb).inv ((colimitCocone E).ι.app n x) =
      (colimitCocone D).ι.app (n + 1) (b n x) :=
  ConcreteCategory.congr_hom (colimitIso_inv_ι D E a b ha hb n) x

/-- The forward quotient function is the supplied stage map on every representative. -/
theorem colimitIso_hom_mk (n : ℕ) (x : D.obj n) :
    (colimitIso D E a b ha hb).hom (G.mk (F := D) ⟨n, x⟩) =
      G.mk (F := E) ⟨n, a n x⟩ :=
  colimitIso_hom_ι_apply D E a b ha hb n x

/-- The inverse quotient function uses exactly the supplied successor-stage map. -/
theorem colimitIso_inv_mk (n : ℕ) (x : E.obj n) :
    (colimitIso D E a b ha hb).inv (G.mk (F := E) ⟨n, x⟩) =
      G.mk (F := D) ⟨n + 1, b n x⟩ :=
  colimitIso_inv_ι_apply D E a b ha hb n x

/-- The inverse also equals the induced `b` map followed by the original successor comparison. -/
theorem inverse_eq_colimitMap_comp_successor :
    inverse D E a b ha hb =
      natQuotientColimit.map (bNatTrans D E a b ha hb) ≫ (successorComparisonIso D).hom := by
  apply (colimitCoconeIsColimit E).hom_ext
  intro n
  have hi := inverse_ι D E a b ha hb n
  have hf := qfac (bNatTrans D E a b ha hb) n
  have hs := successorComparisonIso_hom_ι D n
  exact hi.trans
    ((congrArg (fun f => b n ≫ f) hs).symm.trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (successorComparisonIso D).hom) hf).symm.trans
          (Category.assoc _ _ _))))

/-- A caller's existing transformation induces this same full forward colimit map. -/
theorem colimitIso_hom_eq_colimitMap (α : D ⟶ E) (hα : ∀ n, α.app n = a n) :
    (colimitIso D E a b ha hb).hom = natQuotientColimit.map α := by
  have h : aNatTrans D E a b ha hb = α := by
    apply NatTrans.ext
    funext n
    exact (hα n).symm
  exact congrArg natQuotientColimit.map h

variable {D' E' : ℕ ⥤ GrpCat.{u}}
  (a' : ∀ n, D'.obj n ⟶ E'.obj n) (b' : ∀ n, E'.obj n ⟶ D'.obj (n + 1))
  (ha' : ∀ n, a' n ≫ b' n = step D' n)
  (hb' : ∀ n, b' n ≫ a' (n + 1) = step E' n)

/-- Forward naturality follows from the actual square at every stage. -/
theorem colimitIso_hom_naturality (α : D ⟶ D') (β : E ⟶ E')
    (h : ∀ n, α.app n ≫ a' n = a n ≫ β.app n) :
    natQuotientColimit.map α ≫ (colimitIso D' E' a' b' ha' hb').hom =
      (colimitIso D E a b ha hb).hom ≫ natQuotientColimit.map β := by
  have hn : α ≫ aNatTrans D' E' a' b' ha' hb' = aNatTrans D E a b ha hb ≫ β := by
    apply NatTrans.ext
    funext n
    exact h n
  exact (natQuotientColimit.map_comp α (aNatTrans D' E' a' b' ha' hb')).symm.trans
    ((congrArg (fun f => natQuotientColimit.map f) hn).trans
      (natQuotientColimit.map_comp (aNatTrans D E a b ha hb) β))

/-- Inverse naturality follows from the actual successor-stage square for `b`. -/
theorem colimitIso_inv_naturality (α : D ⟶ D') (β : E ⟶ E')
    (h : ∀ n, β.app n ≫ b' n = b n ≫ α.app (n + 1)) :
    natQuotientColimit.map β ≫ (colimitIso D' E' a' b' ha' hb').inv =
      (colimitIso D E a b ha hb).inv ≫ natQuotientColimit.map α := by
  apply (colimitCoconeIsColimit E).hom_ext
  intro n
  have hf := qfac β n
  have hi' := colimitIso_inv_ι D' E' a' b' ha' hb' n
  have hf' := qfac α (n + 1)
  have hi := colimitIso_inv_ι D E a b ha hb n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (colimitIso D' E' a' b' ha' hb').inv) hf).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => β.app n ≫ f) hi').trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ (colimitCocone D').ι.app (n + 1)) (h n)).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun f => b n ≫ f) hf').symm.trans
                  ((Category.assoc _ _ _).symm.trans
                    ((congrArg (fun f => f ≫ natQuotientColimit.map α) hi).symm.trans
                      (Category.assoc _ _ _))))))))))

end GrpCat.FilteredInterleaving
