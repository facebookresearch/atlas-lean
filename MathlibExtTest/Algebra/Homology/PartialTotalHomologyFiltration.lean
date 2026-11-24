/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalHomologyFiltration

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (n : ℕ) :
    Filtration ((B.total (ComplexShape.down ℕ)).homology n) EInt :=
  B.partialTotalHomologyFiltration n

example (n : ℕ) (a : EInt) :
    (B.partialTotalHomologyFiltration n).ι.app a =
      image.ι ((B.partialTotalHomologyToTotal n).app a) :=
  B.partialTotalHomologyFiltration_ι_app n a

example (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ≅
      image (HomologicalComplex.homologyMap (B.partialTotalι p) n) :=
  B.partialTotalHomologyFiltrationObjIsoImage n p

example (n p : ℕ) :
    (B.partialTotalHomologyFiltrationObjIsoImage n p).hom ≫
        image.ι (HomologicalComplex.homologyMap (B.partialTotalι p) n) =
      (B.partialTotalHomologyFiltration n).ι.app ((p : ℤ) : EInt) :=
  B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι n p

example (n : ℕ) :
    IsZero ((B.partialTotalHomologyFiltration n).obj ⊥) :=
  B.isZero_partialTotalHomologyFiltration_obj_bot n

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app ⊤) :=
  B.partialTotalHomologyFiltration_ι_app_top_isIso n

example (n : ℕ) {a b : EInt} (h : a ≤ b) :
    (B.partialTotalHomologyFiltration n).diagram.map (homOfLE h) ≫
        (B.partialTotalHomologyFiltration n).ι.app b =
      (B.partialTotalHomologyFiltration n).ι.app a :=
  B.partialTotalHomologyFiltration_map_comp_ι n h

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app
      (((n : ℤ) : EInt))) :=
  B.partialTotalHomologyFiltration_exhaustive_at_degree n

example :
    IsIso ((B.partialTotalHomologyFiltration 0).ι.app
      (((0 : ℤ) : EInt))) :=
  B.partialTotalHomologyFiltration_exhaustive_at_degree 0

end HomologicalComplex₂

end
