/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidNativeWordValueRecovery
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverRank

/-!
# Every actual original nonroot cover vertex has its native parent

The complete reduced original label word is split before its actual
last original signed generator. Its full original admissible prefix
gives the SAME native groupoid parent path. The original generator
and actual inverse relation give one original cover edge to the parent.
No parent, tree or weak conclusion is supplied as a premise.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- Every SAME original nonzero cover word has a full original parent
word and original generating edge, retaining both native paths. -/
theorem cover_parent_exists (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    ∃ b : CoverVertex V z,
      (Nonempty (CoverArrow V z b a) ∨ Nonempty (CoverArrow V z a b)) ∧
      CoverVertex.word V z b = (CoverVertex.word V z a).dropLast ∧
        CoverVertex.rank V z b + 1 = CoverVertex.rank V z a := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  let L := CoverVertex.word V z a
  have hL : L ≠ [] := by
    intro h
    change 0 < L.length at ha
    rw [h] at ha
    exact Nat.not_lt_zero _ ha
  let t := L.getLast hL
  have he : L.dropLast ++ [t] = L := List.dropLast_append_getLast hL
  have had : Admissible V z (L.dropLast ++ [t]) a.target :=
    he.symm ▸ CoverVertex.word_admissible V z a
  obtain ⟨m, hpre, htail⟩ := (Admissible.append_iff V L.dropLast [t]).mp had
  let b : CoverVertex V z := ⟨m, hpre.value⟩
  have hred : FreeGroup.IsReduced L.dropLast := (normalWord_isReduced V a.path).infix
    L.dropLast_prefix.isInfix
  have hbword : CoverVertex.word V z b = L.dropLast :=
    Admissible.normalWord_value_of_reduced V hpre hred
  have hlength : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a := by
    change (CoverVertex.word V z b).length + 1 = L.length
    rw [hbword, List.length_dropLast]
    change 0 < L.length at ha
    omega
  have hvalue : hpre.value ≫ htail.value = a.path :=
    (Admissible.value_append V hpre htail).symm.trans
      ((value_eq_of_wordEq V he (Admissible.append V hpre htail)
        (CoverVertex.word_admissible V z a)).trans (normalWord_value_recovery V a.path))
  have hsource := (Admissible.cons_iff V t []).mp htail
  have htarget := (Admissible.nil_iff V _ _).mp hsource.2
  rcases ht : t with ⟨⟨x, y, g⟩, sign⟩
  cases sign
  · rw [ht] at hsource htarget
    have hm : m = y := hsource.1
    have hx : x = a.target := htarget
    subst m
    subst x
    have hg : htail.value = Groupoid.inv ((Quiver.FreeGroupoid.of V).map g) :=
      Admissible.value_path V htail g.toNegPath
        ((signedPathLabels_toPath V (.inr g)).trans (congrArg List.singleton ht.symm))
    have htri : a.path ≫ (Quiver.FreeGroupoid.of V).map g = b.path := by
      have h := congrArg (fun f => f ≫ (Quiver.FreeGroupoid.of V).map g) hvalue
      have hm : (hpre.value ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map g)) ≫
          (Quiver.FreeGroupoid.of V).map g = hpre.value :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun f => hpre.value ≫ f)
            (Groupoid.inv_comp ((Quiver.FreeGroupoid.of V).map g))).trans
            (Category.comp_id _))
      have hh : (hpre.value ≫ htail.value) ≫ (Quiver.FreeGroupoid.of V).map g = hpre.value :=
        (congrArg (fun f => (hpre.value ≫ f) ≫ (Quiver.FreeGroupoid.of V).map g) hg).trans hm
      exact h.symm.trans hh
    exact ⟨b, Or.inr ⟨⟨g, htri⟩⟩, hbword, hlength⟩
  · rw [ht] at hsource htarget
    have hm : m = x := hsource.1
    have hy : y = a.target := htarget
    subst m
    subst y
    have hg : htail.value = (Quiver.FreeGroupoid.of V).map g :=
      (Admissible.value_path V htail g.toPosPath ((signedPathLabels_toPath V (.inl g)).trans
        (congrArg
        List.singleton ht.symm))).trans
        (signedPathValue_positive V g)
    have htri : b.path ≫ (Quiver.FreeGroupoid.of V).map g = a.path :=
      (congrArg (fun f => b.path ≫ f) hg).symm.trans hvalue
    exact ⟨b, Or.inl ⟨⟨g, htri⟩⟩, hbword, hlength⟩

end Quiver.FreeGroupoid.OriginalWords
