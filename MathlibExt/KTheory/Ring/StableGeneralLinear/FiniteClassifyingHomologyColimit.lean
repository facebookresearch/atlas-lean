/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingColimit
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.SequentialColimits
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Homology of the ORIGINAL stable BGL finite-stage cofan

The existing finite nerve cofan is colimiting in every simplicial degree.
Exact filtered colimits of abelian groups and the existing chain-colimit
functor then give the canonical all-degree homology comparison, retaining
EVERY original finite-to-stable injection. The original problem semiring and
all group elements are unchanged; AsSmall is used only for the small indexing
category in the exact-colimit proof.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The ORIGINAL finite nerve cofan after applying fixed-coefficient homology
in an arbitrary degree. -/
public def finiteBGLHomologyCocone (A : AddCommGrpCat.{u}) (q : ℕ) :
    Cocone (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) :=
  (SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).mapCocone (finiteBGLNerveCocone R)

/-- Every-degree homology of the ORIGINAL stable BGL nerve is the colimit of
the ORIGINAL finite-stage homology diagram. Exactness is derived internally. -/
public def finiteBGLHomologyCoconeIsColimit (A : AddCommGrpCat.{u}) (q : ℕ) :
    IsColimit (finiteBGLHomologyCocone R A q) :=
  isColimitOfPreserves (SSet.homologyFunctor (C := AddCommGrpCat.{u})
    A q) (finiteBGLNerveCoconeIsColimit R)

/-- The actual finite-stage homology colimit maps isomorphically to homology
of the ORIGINAL stable-GL nerve in every degree. -/
public def finiteBGLHomologyColimitIso (A : AddCommGrpCat.{u}) (q : ℕ) :
    colimit (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) ≅
      (nerve (ClassifyingCategory R)).homology (C := AddCommGrpCat.{u}) A q :=
  colimit.isoColimitCocone
    ⟨finiteBGLHomologyCocone R A q, finiteBGLHomologyCoconeIsColimit R A q⟩

/-- Every source injection is the SAME finite-to-stable nerve homology map
under the canonical colimit isomorphism. -/
public theorem finiteBGLHomologyColimitIso_ι (A : AddCommGrpCat.{u}) (q n : ℕ) :
    colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
        (finiteBGLHomologyColimitIso R A q).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (finiteToStableCategoryMap R n).toFunctor) A q := by
  have h := colimit.isoColimitCocone_ι_hom
    ⟨finiteBGLHomologyCocone R A q, finiteBGLHomologyCoconeIsColimit R A q⟩ n
  change colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
      (finiteBGLHomologyColimitIso R A q).hom =
    SSet.homologyMap (C := AddCommGrpCat.{u}) ((finiteBGLNerveCocone R).ι.app n) A q at h
  exact h.trans (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q)
    (finiteBGLNerveCocone_ι R n))

end AlgebraicKTheory.StableGL
