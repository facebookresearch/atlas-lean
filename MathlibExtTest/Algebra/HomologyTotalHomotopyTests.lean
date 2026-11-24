/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.TotalHomotopy

/-! # Tests for totalized bicomplex homotopies -/

@[expose] public section

#check HomologicalComplex₂.totalHomotopy₁Hom
#check HomologicalComplex₂.ιTotal_totalHomotopy₁Hom
#check HomologicalComplex₂.totalMapHomotopy₁
#check HomologicalComplex₂.flipMap
#check HomologicalComplex₂.totalFlipIso_hom_naturality
#check HomologicalComplex₂.flipConjugate_eq_totalMap
#check HomologicalComplex₂.totalMapHomotopy₂

end
