/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData
public import MathlibExt.AlgebraicTopology.SingularHomology.Excision.Excision
public import MathlibExt.CategoryTheory.NatIso

/-!
# Excision for integer-graded singular homology
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w u

variable [UnivLE.{w, u}]

noncomputable instance singularHomologyIntData_isExcisive
    (R : AddCommGrpCat.{u}) :
    (singularHomologyIntData AddCommGrpCat.{u} R :
      TopPair.HomologyTheoryData.{w} AddCommGrpCat.{u}).IsExcisive where
  isIso_map_excision := by
    intro z X A B h
    exact NatIso.isIso_map_int_of_nat
      (fun n => relativeSingularHomologyFunctor AddCommGrpCat.{u} R n)
      (relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R)
      (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R)
      (TopPair.excisionHom X A B)
      (fun n => by
        change IsIso ((excisionHomologyCoefficientNatIso.{w, u}
          X A B h n).hom.app R)
        infer_instance)
      (fun i hi => isZero_relativeSingularHomologyIntFunctor_of_neg
        AddCommGrpCat.{u} R i hi (TopPair.excisionSource X A B))
      (fun i hi => isZero_relativeSingularHomologyIntFunctor_of_neg
        AddCommGrpCat.{u} R i hi (TopPair.excisionTarget X A)) z

end AlgebraicTopology
