/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex

/-!
# Original rank-cell readers for an indexed pairing core

The indexed type-II simplex determines exactly the original cell
size, missing-face index and full attaching simplex. The original
attaching map agrees after the literal proved dimension transport.
No rank, simplex or face index is replaced.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial

namespace SSet.Subcomplex.PairingCore

private theorem index_val_eq_of_eq {X : SSet.{u}} {x y x' y' : X.S}
    (hx : x = x') (hy : y = y')
    (h : S.IsUniquelyCodimOneFace x y) (h' : S.IsUniquelyCodimOneFace x' y')
    {d d' : ℕ} (hd : x.dim = d) (hd' : x'.dim = d') (hdd : d = d') :
    (h.index hd).val = (h'.index hd').val := by
  cases hx
  cases hy
  cases hdd
  rfl

private theorem simplex_map_eq_of_eq {X : SSet.{u}} {A : X.Subcomplex} {x y : A.N} (h : x = y) :
    yonedaEquiv.symm x.simplex =
      eqToHom (congrArg (fun d => (Δ[d] : SSet.{u})) (congrArg (fun z : A.N => z.dim) h)) ≫
        yonedaEquiv.symm y.simplex := by
  subst y
  simp only [eqToHom_refl, Category.id_comp]

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper]
    {ι : Type v} [LinearOrder ι] (f : h.pairing.RankFunction ι)
    (s : h.ι) {j : ι} (hs : f.rank (h.equivII s) = j)

omit [h.IsProper] in
/-- The native original indexed rank cell has exactly the supplied core dimension. -/
theorem rankCell_dim :
    (⟨h.equivII s, hs⟩ : f.Cell j).dim = h.dim s := rfl

/-- The actual missing-face index has exactly the same value as the original core index. -/
theorem rankCell_index_val :
    (⟨h.equivII s, hs⟩ : f.Cell j).index.val = (h.index s).val := by
  let c : f.Cell j := ⟨h.equivII s, hs⟩
  have hx : c.s.val.toS = (h.type₂ s).toS := rfl
  have hy : (h.pairing.p c.s).val.toS = (h.type₁ s).toS :=
    congrArg (fun z : A.N => z.toS) (h.type₁_pairing s).symm
  have hv := index_val_eq_of_eq hx hy (h.pairing.isUniquelyCodimOneFace c.s)
    (h.isUniquelyCodimOneFace s) rfl rfl (rankCell_dim h f s hs)
  exact hv.trans (congrArg Fin.val (h.isUniquelyCodimOneFace_index s))

/-- The whole original missing-face index agrees with the indexed pairing-core index. -/
theorem rankCell_index :
    (⟨h.equivII s, hs⟩ : f.Cell j).index = h.index s := by
  apply Fin.ext
  exact rankCell_index_val h f s hs

/-- The original attaching map is the same entire core simplex after the proved literal
  source-dimension transport. -/
theorem rankCell_map :
    (⟨h.equivII s, hs⟩ : f.Cell j).map =
      eqToHom (congrArg (fun d => (Δ[d + 1] : SSet.{u})) (rankCell_dim h f s hs)) ≫
        yonedaEquiv.symm (h.simplex s) := by
  let c : f.Cell j := ⟨h.equivII s, hs⟩
  let z : A.N := (h.pairing.p c.s).val.cast (h.pairing.dim_p c.s)
  have hz : z = h.type₁ s := (N.cast_eq_self _ _).trans (h.type₁_pairing s).symm
  exact simplex_map_eq_of_eq hz

end SSet.Subcomplex.PairingCore

namespace SSet.Subcomplex.Pairing.RankFunction.Cell

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing} [P.IsProper]
    {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι) {j : ι} (c : f.Cell j)

/-- The original horn-to-stage map reads exactly the same whole edge as the native attaching
  simplex. -/
theorem mapHorn_app_ι (e : c.horn.toSSet _⦋1⦌) :
    (f.filtration j).ι.app (Opposite.op ⦋1⦌) (c.mapHorn.app (Opposite.op ⦋1⦌) e) =
      c.map.app (Opposite.op ⦋1⦌) (c.horn.ι.app (Opposite.op ⦋1⦌) e) :=
  ConcreteCategory.congr_hom (congr_app c.mapHorn_ι (Opposite.op ⦋1⦌)) e

end SSet.Subcomplex.Pairing.RankFunction.Cell
