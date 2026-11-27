/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.DFinsupp.BigOperators

/-!
# Finite support in an actual additive coproduct cofan

The standard DFinsupp summation map to the given cofan point is epimorphic:
the original cofan universal property cancels every pair of maps agreeing
on its image. AddCommGrpCat's actual epi/surjectivity theorem then gives a
finite supporting vector. No coproduct-object identification is assumed.
-/

noncomputable section

open CategoryTheory Limits

universe u v

public section

namespace CategoryTheory.Limits

/-- Every element of an actual colimit cofan is a finite sum through its
ORIGINAL injections. The index and additive carrier universes stay explicit. -/
theorem IsColimit.exists_finite_sum
    {I : Type u} {F : I → AddCommGrpCat.{max u v}}
    {V : AddCommGrpCat.{max u v}} {ι : ∀ i, F i ⟶ V}
    (hι : IsColimit (Cofan.mk V ι)) (y : V) :
    ∃ (s : Finset I) (x : ∀ i, F i), y = ∑ i ∈ s, ι i (x i) := by
  classical
  let T : AddCommGrpCat.{max u v} := AddCommGrpCat.of (Π₀ i : I, F i)
  let φ : (Π₀ i : I, F i) →+ V := DFinsupp.sumAddHom (fun i => (ι i).hom)
  let f : T ⟶ V := AddCommGrpCat.ofHom φ
  have hBasis (i : I) :
      AddCommGrpCat.ofHom (DFinsupp.singleAddHom (fun j => F j) i) ≫ f = ι i := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFinsupp.sumAddHom_single (fun j => (ι j).hom) i x
  have hf : Epi f := by
    refine { left_cancellation := ?_ }
    intro W g h hgh
    apply hι.hom_ext
    rintro ⟨i⟩
    change ι i ≫ g = ι i ≫ h
    let a := AddCommGrpCat.ofHom (DFinsupp.singleAddHom (fun j => F j) i)
    have ha : a ≫ f = ι i := hBasis i
    calc
      ι i ≫ g = (a ≫ f) ≫ g := congrArg (fun k => k ≫ g) ha.symm
      _ = a ≫ (f ≫ g) := Category.assoc a f g
      _ = a ≫ (f ≫ h) := congrArg (fun k => a ≫ k) hgh
      _ = (a ≫ f) ≫ h := (Category.assoc a f h).symm
      _ = ι i ≫ h := congrArg (fun k => k ≫ h) ha
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective f).mp hf y
  refine ⟨z.support, fun i => z i, ?_⟩
  have hSum : f z = ∑ i ∈ z.support, ι i (z i) := by
    change DFinsupp.sumAddHom (fun i => (ι i).hom) z = _
    exact DFinsupp.sumAddHom_apply (fun i => (ι i).hom) z
  exact hz.symm.trans hSum

end CategoryTheory.Limits

end
