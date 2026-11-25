/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsDiagonal

/-!
# Every original BK coefficient in the full elements diagonal

The complete weighted chain and its original source coefficient give
the same native elements chain. Every vertex retains its entire
original coefficient transport, and the first is the source value.
-/

noncomputable section

universe uJ vJ

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- Every whole original weighted coefficient is the same complete canonical elements chain. -/
theorem bkHocolimElementsDiagonalIso_weighted (D : J ⥤ SSet.{max uJ vJ})
    (n : ℕ) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
        (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D (op ⦋n⦌))).hom.app (op ⦋n⦌)
          ⟨p.1, x, p.2⟩ := by
  have h := ConcreteCategory.congr_hom
    (terminalWeightRowIso_hom_rowIncl D (op ⦋n⦌) n p) x
  rw [wbarRowIncl_eq_wbarIncl_app] at h
  change (terminalWeightRowIso D (op ⦋n⦌)).hom.app (op ⦋n⦌)
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      ⟨p.1, x, p.2⟩ at h
  change (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D (op ⦋n⦌))).hom.app (op ⦋n⦌)
      ((terminalWeightRowIso D (op ⦋n⦌)).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)) = _
  exact congrArg ((CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D (op
    ⦋n⦌))).hom.app (op ⦋n⦌)) h

/-- Every vertex retains its full original indexing object and original coefficient transport. -/
theorem bkHocolimElementsDiagonalIso_vertex (D : J ⥤ SSet.{max uJ vJ})
    (n : ℕ) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    ((bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)).obj i =
        (wbarDegreeCoefficient D (op ⦋n⦌)).elementsMk (p.1.obj i)
          ((D.map (p.1.map' 0 i.val)).app (op ⦋n⦌) x) :=
  (congrArg (fun F => F.obj i) (bkHocolimElementsDiagonalIso_weighted D n p x)).trans
    (CategoryBar.replNerveSimplicialIso_vertex (wbarDegreeCoefficient D (op ⦋n⦌)) n p.1 x p.2 i)

/-- The first original elements vertex is literally the full original source coefficient. -/
theorem bkHocolimElementsDiagonalIso_first (D : J ⥤ SSet.{max uJ vJ})
    (n : ℕ) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    ((bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)).obj 0 =
        (wbarDegreeCoefficient D (op ⦋n⦌)).elementsMk p.1.left x :=
  (congrArg (fun F => F.obj 0) (bkHocolimElementsDiagonalIso_weighted D n p x)).trans
    (CategoryBar.replNerveSimplicialIso_first (wbarDegreeCoefficient D (op ⦋n⦌)) n p.1 x p.2)

end SSet
