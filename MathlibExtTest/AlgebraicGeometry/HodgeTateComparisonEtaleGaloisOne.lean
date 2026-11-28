/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisOne

namespace MathlibExtTest.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisOne

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open WantedExt.AlgebraicGeometry.HodgeTateComparison

-- The identity operator acts trivially at the prime 2 in degree 0.
example [Fact (Nat.Prime 2)] (X : Over (Spec (CommRingCat.of.{0} ℚ_[2]))) :
    etaleGalois 2 X 1 0 = LinearMap.id :=
  etaleGalois_one 2 X 0

-- Pointwise form: the identity operator fixes every cohomology class.
example (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))
    (n : ℕ) (a : Etale p X n) : etaleGalois p X 1 n a = a := by
  simp [etaleGalois_one p X n]

-- The completed étale operators inherit the identity law.
example (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))
    (n : ℕ) : completedEtaleGalois p X 1 n = LinearMap.id :=
  completedEtaleGalois_one p X n (etaleGalois_one p X n)

end MathlibExtTest.AlgebraicGeometry.HodgeTateComparisonEtaleGaloisOne
