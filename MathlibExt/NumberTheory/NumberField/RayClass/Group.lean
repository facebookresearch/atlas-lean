/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayGroup

/-!
# Ray class groups as quotients (N404)

The ray class group of a modulus `m` is the quotient of the group of
fractional ideals coprime to `m` by the ray group.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Ray class group.** The ray class group of a modulus $\mathfrak m$ of a number field $K$ is
the quotient of the group of nonzero fractional ideals of $K$ coprime to the finite part of
$\mathfrak m$ by the ray group of $\mathfrak m$. -/
abbrev RayClassGroup (m : Modulus K) :=
  ↥(coprimeFractionalIdeals m) ⧸ rayGroup m

/-- **Ray class map.** For a modulus $\mathfrak m$ of a number field $K$, the ray class map is the
canonical quotient homomorphism from the group of nonzero fractional ideals of $K$ coprime to the
finite part of $\mathfrak m$ onto the ray class group of $\mathfrak m$, sending each such ideal to
its class modulo the ray group of $\mathfrak m$. -/
def rayClassMap (m : Modulus K) :
    coprimeFractionalIdeals m →* RayClassGroup m :=
  QuotientGroup.mk' (rayGroup m)

theorem rayClassMap_surjective (m : Modulus K) :
    Function.Surjective (rayClassMap (K := K) m) :=
  QuotientGroup.mk'_surjective _

@[simp] theorem rayClassMap_ker (m : Modulus K) :
    MonoidHom.ker (rayClassMap (K := K) m) = rayGroup m :=
  QuotientGroup.ker_mk' _

@[simp] theorem rayClassMap_eq_one_iff (m : Modulus K)
    (x : coprimeFractionalIdeals m) :
    rayClassMap m x = 1 ↔ x ∈ rayGroup m :=
  QuotientGroup.eq_one_iff x

theorem rayClassMap_eq_rayClassMap_iff (m : Modulus K)
    (a b : coprimeFractionalIdeals m) :
    rayClassMap m a = rayClassMap m b ↔ a / b ∈ rayGroup m :=
  by simpa [rayClassMap, RayClassGroup] using
    (QuotientGroup.eq_iff_div_mem (N := rayGroup m) (x := a) (y := b))

end Modulus
end NumberField
