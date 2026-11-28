/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Functorial enveloping-algebra maps and the scalar augmentation

Let R be a commutative ring and L an R-Lie algebra. A Lie homomorphism
f : L → L′ induces an R-algebra map U(f) : U_R(L) → U_R(L′) determined
by U(f)(ι(x)) = ι(f(x)). These maps preserve identities and composition.

The scalar augmentation ε_L : U_R(L) → R is the unique R-algebra map
annihilating every Lie generator. It satisfies ε_L(ι(x)) = 0 and
ε_L(algebraMap(r)) = r, and is natural:
ε_(L′) ∘ U(f) = ε_L. The ring and all Lie-carrier worlds are independent,
and the construction applies to arbitrary R-Lie algebras.
-/

@[expose] public section

noncomputable section

universe u v v' v''

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

attribute [local instance] LieRing.ofAssociativeRing

/-- For a commutative ring R and a Lie homomorphism
f : L →ₗ⁅R⁆ L′, the R-algebra map U_R(L) → U_R(L′) is determined
by ι_L(x) ↦ ι_(L′)(f(x)). The Lie-carrier universes of L and L′
are independent. -/
def map (f : L →ₗ⁅R⁆ L') : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L' :=
  lift R ((ι R).comp f)

theorem map_ι (f : L →ₗ⁅R⁆ L') (x : L) : map R f (ι R x) = ι R (f x) :=
  lift_ι_apply R ((ι R).comp f) x

/-- For a commutative ring R and an R-Lie algebra L, the
enveloping-algebra map induced by id_L is id_(U_R(L)) as an
R-algebra homomorphism. -/
@[simp]
theorem map_id : map R (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R _ := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    map_ι, LieHom.id_apply, AlgHom.id_apply]

/-- For a commutative ring R and Lie homomorphisms
f : L → L′ and g : L′ → L″, the enveloping maps satisfy
U(g ∘ f) = U(g) ∘ U(f). The carrier worlds of all three
Lie algebras are independent. -/
theorem map_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    map_ι, AlgHom.comp_apply]

/-- For a commutative ring R and an R-Lie algebra L, the
augmentation ε_L : U_R(L) →ₐ[R] R is induced by the zero Lie map
L → R. It sends each generator ι(x) to zero and each scalar
algebraMap(r) to r. -/
def augmentation (L : Type v) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  lift R (0 : L →ₗ⁅R⁆ R)

theorem augmentation_ι (x : L) : augmentation R L (ι R x) = 0 :=
  lift_ι_apply R (0 : L →ₗ⁅R⁆ R) x

/-- For a commutative ring R and an R-Lie algebra L, if an
R-algebra homomorphism ε : U_R(L) → R satisfies ε(ι(x)) = 0
for every x ∈ L, then ε equals the scalar augmentation ε_L. -/
theorem augmentation_unique (ε : UniversalEnvelopingAlgebra R L →ₐ[R] R)
    (hε : ∀ x : L, ε (ι R x) = 0) : ε = augmentation R L := by
  apply hom_ext
  apply LieHom.ext
  intro x
  simpa only [LieHom.coe_comp, AlgHom.coe_toLieHom, Function.comp_apply,
    augmentation_ι] using hε x

/-- For a commutative ring R and a Lie homomorphism f : L → L′,
the induced R-algebra map U(f) satisfies
ε_(L′) ∘ U(f) = ε_L. The ring, source Lie carrier and target Lie
carrier may have independent universes. -/
theorem augmentation_naturality (f : L →ₗ⁅R⁆ L') :
    (augmentation R L').comp (map R f) = augmentation R L := by
  apply augmentation_unique
  intro x
  simp only [AlgHom.comp_apply, map_ι, augmentation_ι]

end UniversalEnvelopingAlgebra
