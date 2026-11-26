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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.BoundedSupport
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Coordinates

/-!
# Single-coordinate insertion in Hom cochains

Let R be a commutative ring and P,J integer R-module cochain complexes in a common carrier
universe. For p+a=j, an R-linear map P^p → J^j gives a degree-a cochain supported at that
source coordinate.

Insertion is R-linear and retains the given map at its supported coordinate. Different
target-degree presentations of the same coordinate give the same single cochain. No
boundedness, finite generation, or projectivity of the complexes is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Let R be a commutative ring, P,J integer cochain complexes in ModuleCat.{v} R, and a,p,j ∈ ℤ
with p+a=j. Single-coordinate insertion defines an R-linear map Hom_R(P^p,J^j) → C^a(P,J). Its
value has the given component at source p and zero components at other source degrees. -/
def cochainSingleLinear (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a p j : ℤ) (hpj : p + a = j) :
    (P.X p →ₗ[R] J.X j) →ₗ[R] Cochain P J a where
  toFun f := Cochain.single (ModuleCat.ofHom f) a
  map_add' f g := by
    apply Cochain.ext
    intro p' j' hpj'
    by_cases hp : p' = p
    · subst p'
      have hj : j' = j := by omega
      subst hj
      simp only [Cochain.single_v, Cochain.add_v]
      rfl
    · rw [Cochain.add_v,
        Cochain.single_v_eq_zero (ModuleCat.ofHom (f + g)) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom f) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom g) a p' j' hpj' hp,
        zero_add]
  map_smul' r f := by
    apply Cochain.ext
    intro p' j' hpj'
    by_cases hp : p' = p
    · subst p'
      have hj : j' = j := by omega
      subst hj
      simp only [RingHom.id_apply, Cochain.single_v, Cochain.smul_v]
      rfl
    · rw [Cochain.smul_v,
        Cochain.single_v_eq_zero (ModuleCat.ofHom (r • f)) a p' j' hpj' hp,
        Cochain.single_v_eq_zero (ModuleCat.ofHom f) a p' j' hpj' hp,
        smul_zero]

/-- For a commutative ring R, integer R-module cochain complexes P,J, p+a=j, and f : P^p →ₗ[R]
J^j, the (p,j)-coordinate of cochainSingleLinear(f) equals ModuleCat.ofHom(f). Thus insertion
preserves the given map on its supported degree. -/
theorem cochainSingleLinear_v (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a p j : ℤ) (hpj : p + a = j) (f : P.X p →ₗ[R] J.X j) :
    (cochainSingleLinear R P J a p j hpj f).v p j hpj = ModuleCat.ofHom f :=
  Cochain.single_v _ _ _

/-- Let R be a commutative ring, P,J integer R-module cochain complexes, f ∈ C^a(P,J), and p+a=j
and p+a=j′. The degree-a single cochains formed from f_{p,j} and f_{p,j′} are equal. The
equality uses the same source coordinate and the canonical identification of the two
target-degree presentations. -/
theorem cochain_single_coordinate_eq (P J : CochainComplex (ModuleCat.{v} R) ℤ)
    (a : ℤ) (f : Cochain P J a) (p j j' : ℤ)
    (hpj : p + a = j) (hpj' : p + a = j') :
    Cochain.single (f.v p j hpj) a = Cochain.single (f.v p j' hpj') a := by
  subst j
  subst j'
  rfl

end CochainComplex.ModuleTensor
