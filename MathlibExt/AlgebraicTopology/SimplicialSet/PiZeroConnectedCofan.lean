/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Connected components of coproducts of connected simplicial sets

Let `J : Type u`, let `K : J → SSet.{u}` be a family of connected simplicial sets, and let `c`
be a colimiting coproduct cofan for `K`. Applying the connected-component functor
`SSet.π₀Functor` to `c` gives a colimiting cofan in types. In particular, components belonging
to different summands remain distinct in the coproduct.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

private abbrev discreteSSet (J : Type u) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj J

private lemma mk_injective_discreteSSet (J : Type u) :
    Function.Injective (π₀.mk (X := discreteSSet J)) := by
  intro x y h
  rw [π₀.mk_eq_mk_iff] at h
  induction h with
  | rel x y h =>
      obtain ⟨e⟩ := h
      simpa [discreteSSet] using e.src_eq.symm.trans e.tgt_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma mapπ₀_const_discreteSSet
    {J : Type u} {X : SSet.{u}} (j : J) (q : π₀ X) :
    mapπ₀ (SSet.const (X := X) (Y := discreteSSet J) j) q =
      π₀.mk (X := discreteSSet J) j := by
  induction q using π₀.rec with
  | mk x => rfl

namespace π₀

/-- Let `J : Type u`, `K : J → SSet.{u}`, and suppose that every `K j` is connected. If `c : Cofan
K` is a coproduct cofan with `hc : IsColimit c`, then `SSet.π₀Functor.mapCocone c` is a
colimit cocone in types. Its legs are the maps on connected components induced by the
coproduct inclusions. -/
noncomputable opaque isColimitMapCoconeOfConnected
    {J : Type u} (K : J → SSet.{u})
    [∀ j, SSet.IsConnected (K j)]
    (c : Cofan K) (hc : IsColimit c) :
    IsColimit (SSet.π₀Functor.mapCocone c) := by
  let labelCofan : Cofan K :=
    Cofan.mk (discreteSSet J)
      (fun j ↦ SSet.const (X := K j) (Y := discreteSSet J) j)
  let labelMap : c.pt ⟶ discreteSSet J := hc.desc labelCofan
  have hlabel (j : J) : c.inj j ≫ labelMap =
      SSet.const (X := K j) (Y := discreteSSet J) j :=
    hc.fac labelCofan ⟨j⟩
  let mappedCofan : Cofan (fun j ↦ π₀ (K j)) :=
    Cofan.mk (π₀ c.pt) (fun j ↦ SSet.π₀Functor.map (c.inj j))
  have hExplicit : IsColimit mappedCofan := by
    apply Nonempty.some
    rw [← Cofan.isColimit_cofanTypes_iff mappedCofan]
    apply CofanTypes.isColimit_mk
    · intro q
      obtain ⟨x, rfl⟩ := q.mk_surjective
      have hc0 := isColimitOfPreserves
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) hc
      obtain ⟨⟨j⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit hc0 x
      refine ⟨j, π₀.mk y, ?_⟩
      change mapπ₀ (c.inj j) (π₀.mk y) = π₀.mk x
      rw [mapπ₀_mk]
      exact congrArg π₀.mk hy
    · intro j
      exact Function.injective_of_subsingleton _
    · intro j k q r h
      have h' := congrArg (mapπ₀ labelMap) h
      change mapπ₀ labelMap (mapπ₀ (c.inj j) q) =
        mapπ₀ labelMap (mapπ₀ (c.inj k) r) at h'
      have hj : mapπ₀ labelMap (mapπ₀ (c.inj j) q) =
          π₀.mk (X := discreteSSet J) j := by
        rw [← mapπ₀_comp_apply, hlabel j,
          mapπ₀_const_discreteSSet]
      have hk : mapπ₀ labelMap (mapπ₀ (c.inj k) r) =
          π₀.mk (X := discreteSSet J) k := by
        rw [← mapπ₀_comp_apply, hlabel k,
          mapπ₀_const_discreteSSet]
      rw [hj, hk] at h'
      exact mk_injective_discreteSSet J h'
  let c' : Cofan K := Cofan.mk c.pt (fun j ↦ c.inj j)
  have hmap' : IsColimit (SSet.π₀Functor.mapCocone c') :=
    (isColimitMapCoconeCofanMkEquiv SSet.π₀Functor K
      (fun j ↦ c.inj j)).symm hExplicit
  exact IsColimit.ofIsoColimit hmap' (Cocone.ext (Iso.refl _))

end π₀
end SSet
