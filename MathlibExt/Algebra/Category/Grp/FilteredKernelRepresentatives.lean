/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Combinatorics.Quiver.ReflQuiver

set_option autoImplicit false
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits

namespace GrpCat.FilteredColimits

section OriginalCanonicalContext
attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- A kernel quotient class has an original representative with null image at a later stage. -/
theorem colimitMap_kernel_representative
    {D E : ℕ ⥤ GrpCat.{v}} (α : D ⟶ E)
    (x : colimit D) (hx : ((colimitCoconeIsColimit D).map (colimitCocone E) α).hom x = 1) :
    ∃ (n m : ℕ) (h : n ≤ m) (a : D.obj n),
      (colimitCocone D).ι.app n a = x ∧ E.map (homOfLE h) (α.app n a) = 1 := by
  let _ : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, 0, 0} (forget GrpCat.{v})
  have hD := isColimitOfPreserves (forget GrpCat.{v}) (colimitCoconeIsColimit D)
  have hE := isColimitOfPreserves (forget GrpCat.{v}) (colimitCoconeIsColimit E)
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective_of_isColimit hD x
  change (colimitCocone D).ι.app n a = x at ha
  have heq : (colimitCocone E).ι.app n (α.app n a) = (colimitCocone E).ι.app n 1 := by
    calc
      (colimitCocone E).ι.app n (α.app n a) =
          (colimitCoconeIsColimit D).map (colimitCocone E) α ((colimitCocone D).ι.app n a) :=
        (ConcreteCategory.congr_hom
          ((colimitCoconeIsColimit D).ι_map (colimitCocone E) α n) a).symm
      _ = 1 := by rw [ha]; exact hx
      _ = (colimitCocone E).ι.app n 1 := (map_one _).symm
  obtain ⟨m, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hE (α.app n a) (1 : E.obj n)).mp heq
  change E.map f (α.app n a) = E.map f 1 at hf
  rw [map_one] at hf
  refine ⟨n, m, leOfHom f, a, ha, ?_⟩
  exact hf

end OriginalCanonicalContext

end GrpCat.FilteredColimits

namespace CategoryTheory.Limits

/-- A kernel class of the caller's actual continuous Nat group cocones has an original later
null stage.
Both actual cocone points, both IsColimit witnesses and the caller's entire map are retained. -/
theorem originalNatGroupCocone_kernel_stage
    {D E : ℕ ⥤ GrpCat.{v}} (c : Cocone D) (d : Cocone E)
    (hc : IsColimit c) (hd : IsColimit d) (a : D ⟶ E) (f : c.pt ⟶ d.pt)
    (hf : ∀ n, c.ι.app n ≫ f = a.app n ≫ d.ι.app n)
    (x : c.pt) (hx : f.hom x = 1) :
    ∃ (n m : ℕ) (h : n ≤ m) (b : D.obj n),
      (c.ι.app n).hom b = x ∧ (E.map (homOfLE h)).hom ((a.app n).hom b) = 1 := by
  let eC := (GrpCat.FilteredColimits.colimitCoconeIsColimit D).coconePointUniqueUpToIso hc
  let eD := (GrpCat.FilteredColimits.colimitCoconeIsColimit E).coconePointUniqueUpToIso hd
  let mapDE := (GrpCat.FilteredColimits.colimitCoconeIsColimit D).map
    (GrpCat.FilteredColimits.colimitCocone E) a
  have hm : mapDE ≫ eD.hom = eC.hom ≫ f := by
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit D).hom_ext
    intro n
    dsimp only [mapDE]
    rw [← Category.assoc, IsColimit.ι_map,
      Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom,
      ← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (hf n).symm
  let y := eC.inv.hom x
  have hNull : mapDE.hom y = 1 := by
    apply eD.groupIsoToMulEquiv.injective
    have h := congrArg (fun k => k.hom y) hm
    have hInv : eC.hom.hom y = x := ConcreteCategory.congr_hom eC.inv_hom_id x
    exact h.trans ((congrArg f.hom hInv).trans (hx.trans (map_one eD.hom.hom).symm))
  obtain ⟨n, m, h, b, hb, hN⟩ := GrpCat.FilteredColimits.colimitMap_kernel_representative a y hNull
  refine ⟨n, m, h, b, ?_, hN⟩
  have hLeg := ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (GrpCat.FilteredColimits.colimitCoconeIsColimit D) hc n) b
  exact hLeg.symm.trans
    ((congrArg eC.hom.hom hb).trans (ConcreteCategory.congr_hom eC.inv_hom_id x))

end CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- The caller's exact null representative can be chosen beyond every prescribed original stage. -/
theorem originalNatGroupCocone_kernel_later_stage
    {D E : ℕ ⥤ GrpCat.{v}} (c : Cocone D) (d : Cocone E)
    (hc : IsColimit c) (hd : IsColimit d) (a : D ⟶ E) (f : c.pt ⟶ d.pt)
    (hf : ∀ n, c.ι.app n ≫ f = a.app n ≫ d.ι.app n)
    (x : c.pt) (hx : f.hom x = 1) (n₀ : ℕ) :
    ∃ (m : ℕ), n₀ ≤ m ∧ ∃ b : D.obj m,
      (c.ι.app m).hom b = x ∧ (a.app m).hom b = 1 := by
  obtain ⟨n, l, hnl, b, hb, hNull⟩ := originalNatGroupCocone_kernel_stage c d hc hd a f hf x hx
  let m := max n₀ l
  let φ : n ⟶ m := homOfLE (hnl.trans (le_max_right n₀ l))
  let ψ : l ⟶ m := homOfLE (le_max_right n₀ l)
  let z := (D.map φ).hom b
  have hRep : (c.ι.app m).hom z = x :=
    (ConcreteCategory.congr_hom (c.w φ) b).trans hb
  have hNat : (a.app m).hom z = (E.map φ).hom ((a.app n).hom b) :=
    ConcreteCategory.congr_hom (a.naturality φ) b
  have hFac : E.map φ = E.map (homOfLE hnl) ≫ E.map ψ :=
    (E.congr_map (Subsingleton.elim φ ((homOfLE hnl) ≫ ψ))).trans (E.map_comp _ _)
  have hEnd : (E.map φ).hom ((a.app n).hom b) = 1 := by
    rw [hFac]
    exact (congrArg (E.map ψ).hom hNull).trans (map_one _)
  exact ⟨m, le_max_left _ _, z, hRep, hNat.trans hEnd⟩

end CategoryTheory.Limits
