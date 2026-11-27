/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

/-! # Tests for the de Rham complex of a scheme over `F_p`

The constructed differential satisfies the de Rham formula on local generators (in
particular `d a = da` on functions and `d (da) = 0`), squares to zero, is linear over `p`-th
powers, commutes with restriction, and is the only differential. The Witt reduction
`W₂(F_p) → F_p` is the zeroth coordinate.
-/

open CategoryTheory AlgebraicGeometry MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

namespace MathlibExtTest.AlgebraicGeometry.PrimeFieldDeRham

variable (p : ℕ) [Fact p.Prime] (X : PrimeFieldScheme p)

example (i : ℕ) (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U)
    (b : Fin i → X.left.presheaf.obj U) :
    ((Differential.deRham p X).d i).app U (generatorForm p X i U a b) =
      exteriorPower.ιMulti (X.left.presheaf.obj U) (i + 1)
        (fun j => CommRingCat.KaehlerDifferential.d (f := (scalarMap p X).app U)
          ((Fin.cons a b : Fin (i + 1) → X.left.presheaf.obj U) j)) :=
  (Differential.deRham p X).generator i U a b

/-- On functions, `d a = da`. -/
example (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U) :
    ((Differential.deRham p X).d 0).app U (generatorForm p X 0 U a Fin.elim0) =
      exteriorPower.ιMulti (X.left.presheaf.obj U) 1
        (fun _ => CommRingCat.KaehlerDifferential.d (f := (scalarMap p X).app U) a) := by
  rw [(Differential.deRham p X).generator 0 U a Fin.elim0]
  congr 1
  funext j
  fin_cases j
  rfl

/-- Exact forms are closed: `d (1 • db) = d1 ∧ db = 0`. -/
example (U : X.left.Opensᵒᵖ) (b : X.left.presheaf.obj U) :
    ((Differential.deRham p X).d 1).app U (generatorForm p X 1 U 1 ![b]) = 0 := by
  have h1 : CommRingCat.KaehlerDifferential.d (f := (scalarMap p X).app U) 1 = 0 := by
    simpa using (CommRingCat.KaehlerDifferential.D ((scalarMap p X).app U)).d_map 1
  rw [(Differential.deRham p X).generator 1 U 1 ![b]]
  refine Subtype.ext ?_
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, h1,
    map_zero, zero_mul]
  rfl

example (i : ℕ) :
    (Differential.deRham p X).d i ≫ (Differential.deRham p X).d (i + 1) = 0 :=
  (Differential.deRham p X).square i

example (i : ℕ) (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U)
    (x : (formsPresheaf p X i).obj U) :
    deRhamApp p X i U (a ^ p • x) = a ^ p • deRhamApp p X i U x :=
  deRhamApp_pow_smul p X i U a x

example (i : ℕ) {U V : X.left.Opensᵒᵖ} (f : U ⟶ V) (x : (formsPresheaf p X i).obj U) :
    deRhamApp p X i V ((formsPresheaf p X i).map f x) =
      (formsPresheaf p X (i + 1)).map f (deRhamApp p X i U x) :=
  deRhamApp_naturality p X i f x

/-- The de Rham formula determines the differential. -/
example (D : Differential p X) : D = Differential.deRham p X := Differential.eq_deRham p X D

example (x : TruncatedWittVector p 2 (ZMod p)) : wittReduction p x = x.coeff 0 := rfl

end MathlibExtTest.AlgebraicGeometry.PrimeFieldDeRham
