/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalStraightening
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalInnerHornStraightening
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalCells

/-!
# SAME original marked critical lifts of actual native Un maps

Every genuine original coherent-model fibration has all original
critical-cell lifts under the SAME native Un functor. The whole
original marked source and target are retained, even when neither
coefficient diagram is fibrant. A prescribed final-horn square with its
original critical edge marked therefore has the actual original marked
cell lift, retaining the entire original top and bottom maps. No native
filler, source-model fibration or Quillen outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual coherent-model fibrations give every SAME original marked critical-cell lift of their SAME complete
native marked total map, without fibrancy of either diagram. -/
theorem nativeUnstraightening_map_originalMarkedCriticalLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n)
      ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq n
  have hOver := nativeUnstraightening_map_originalCriticalRlp B q hq
  have h : (ofHoms (fun k : ℕ => (nativeOriginalCriticalCell.{u} k).hom)).rlp
      ((nativeUnstraightening B).map q).left :=
    (overCells_rlp_iff nativeOriginalCriticalCell.{u} (max B) ((nativeUnstraightening B).map q)).mp hOver
  exact h _ (ofHoms.mk (f := fun k : ℕ => (nativeOriginalCriticalCell.{u} k).hom) n)

/-- The SAME original final horn, prescribed whole native bottom simplex and original marked critical edge have an
actual original native filler from the genuine target-model fibration. -/
theorem nativeUnstraightening_fill_originalFinalHorn (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ {n : ℕ} (_hn : 1 ≤ n) {i : Fin (n + 2)} (_hi : i = Fin.last (n + 1))
      (t : (horn.{u} (n + 1) i : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
      (b : (Δ[n + 1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet),
      t ≫ ((nativeUnstraightening B).map q).left.hom = (horn.{u} (n + 1) i).ι ≫ b →
      ∀ e : (horn.{u} (n + 1) i : SSet.{u}) _⦋1⦌,
        (horn.{u} (n + 1) i).ι.app (op ⦋1⦌) e =
          stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _) →
        t.app (op ⦋1⦌) e ∈ (nativeUnstraighteningTotal B F).marking →
        ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
          (horn.{u} (n + 1) i).ι ≫ l = t ∧ l ≫ ((nativeUnstraightening B).map q).left.hom = b := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq n hn i hi t b hsq e he hm
  subst i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he' : e = rightHornEdgeSimplex.{u} m := by
    apply Subtype.ext
    exact he
  have ht : t.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} m) ∈ (nativeUnstraighteningTotal B F).marking :=
    he' ▸ hm
  let p := ((nativeUnstraightening B).map q).left
  have hcritical := p.preserve ht
  have hvalue := ConcreteCategory.congr_hom (congr_app hsq (op ⦋1⦌)) (rightHornEdgeSimplex.{u} m)
  have hb : b.app (op ⦋1⦌) ((horn.{u} (m + 2) (Fin.last (m + 2))).ι.app (op ⦋1⦌)
      (rightHornEdgeSimplex.{u} m)) ∈ (nativeUnstraighteningTotal B G).marking := hvalue ▸ hcritical
  let a' := ofCartesianCriticalSource t ht
  let b' := ofCartesianCriticalTarget b hb
  let sq : CommSq a' (cartesianCriticalCell.{u} m) p b' := ⟨Hom.ext hsq⟩
  obtain ⟨l, hl, hr⟩ := (nativeUnstraightening_map_originalMarkedCriticalLifting B q hq m).sq_hasLift sq
  exact ⟨l.hom, congrArg Hom.hom hl, congrArg Hom.hom hr⟩

end SSet.Marked
