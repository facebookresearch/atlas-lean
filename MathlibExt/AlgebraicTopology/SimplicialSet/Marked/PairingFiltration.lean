/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex

/-!
# Original marked filtrations of a regular pairing

The native natural-number rank filtration carries the marking inherited
from the actual target. If all target marks lie in the original source,
its native underlying colimit is the same marked colimit and every
successor inclusion covers the target marks. No critical-horn lifting,
marked weak class or model structure is assumed here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

variable (X : Marked.{u}) (A : X.toSSet.Subcomplex) (P : A.Pairing) [P.IsRegular]

/-- The same actual rank stages retain the original target-inherited marking. -/
def pairingFiltration : ℕ ⥤ Marked.{u} :=
  P.rankFunction.filtration_monotone.functor ⋙ subcomplexFunctor X

/-- The literal original rank-stage inclusions form the marked cocone into the actual target. -/
def pairingFiltrationCocone : Cocone (pairingFiltration X A P) :=
  subcomplexCocone X P.rankFunction.filtration_monotone.functor

/-- The initial marked stage is exactly the original source subcomplex with its inherited marking. -/
def pairingFiltrationIsoBot : (pairingFiltration X A P).obj 0 ≅ comap X A.ι :=
  (subcomplexFunctor X).mapIso (eqToIso P.rankFunction.filtration_bot)

/-- Original mark coverage makes the complete native pairing cocone a genuine marked colimit. -/
def pairingFiltrationIsColimit
    (hA : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ A.obj (op ⦋1⦌)) :
    IsColimit (pairingFiltrationCocone X A P) := by
  apply subcomplexCoconeIsColimit X P.rankFunction.filtration_monotone.functor 0
  · intro e he
    change e ∈ (P.rankFunction.filtration 0).obj (op ⦋1⦌)
    have h : P.rankFunction.filtration 0 = A := P.rankFunction.filtration_bot
    exact (congrArg (fun S : X.toSSet.Subcomplex => e ∈ S.obj (op ⦋1⦌)) h).to_iff.mpr (hA e he)
  · exact P.rankFunction.relativeCellComplex.isColimit

/-- The original marked source inclusion is the actual natural-rank transfinite composition of these same stage maps. -/
def pairingFiltrationTransfiniteComposition
    (hA : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ A.obj (op ⦋1⦌)) :
    CategoryTheory.TransfiniteCompositionOfShape ℕ (comapHom X A.ι) where
  F := pairingFiltration X A P
  isoBot := pairingFiltrationIsoBot X A P
  incl := (pairingFiltrationCocone X A P).ι
  isColimit := pairingFiltrationIsColimit X A P hA
  fac := by
    apply Hom.ext
    change Subcomplex.toSSetFunctor.map (eqToHom P.rankFunction.filtration_bot.symm) ≫
      (P.rankFunction.filtration 0).ι = A.ι
    exact Subcomplex.homOfLE_ι (leOfHom (eqToHom P.rankFunction.filtration_bot.symm))

/-- Every actual successor stage keeps the complete original source marking and covers all later target marks. -/
theorem pairingFiltration_step_markingSurjective
    (hA : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ A.obj (op ⦋1⦌)) (j : ℕ) :
    MarkingSurjective ((pairingFiltration X A P).map (homOfLE (Nat.le_succ j))) :=
  subcomplexFunctor_map_markingSurjective X A hA _ (P.rankFunction.le_filtration j)

end SSet.Marked
