/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Module.Equiv.Defs

@[expose] public section

/-!
# Inversion twist of a group-ring module

For a commutative group `G`, inversion induces a ring involution on the group
ring `R[G]`. This file defines both that involution and the module obtained by
precomposing a group-ring action with it.
-/

noncomputable section

namespace GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

/-- **Inversion on a group ring.** Let $R$ be a commutative ring and $G$ a commutative group.
The inversion of the group ring $R[G]$ is the ring automorphism of $R[G]$ induced by the group
automorphism $g \mapsto g^{-1}$ of $G$: it sends $\sum_g r_g\, g$ to $\sum_g r_g\, g^{-1}$. -/
def inversion : MonoidAlgebra R G ≃+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingEquiv R (MulEquiv.inv G)

/-- **Inversion on basis elements.** Let $R$ be a commutative ring and $G$ a commutative group.
For every $g \in G$ and $r \in R$, the inversion of the group ring $R[G]$ sends $r\, g$ to
$r\, g^{-1}$. -/
@[simp]
theorem inversion_single (g : G) (r : R) :
    inversion R G (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  simp [inversion]

/-- Applying the group-ring inversion twice is the identity. -/
@[simp]
theorem inversion_involution (x : MonoidAlgebra R G) : inversion R G (inversion R G x) = x := by
  ext g
  simp [inversion]

/-- **Inversion twist of a group-ring module.** Let $R$ be a commutative ring, $G$ a commutative
group and $A$ a module over the group ring $R[G]$. The inversion twist of $A$ is a copy of $A$
with the same addition, on which $r \in R[G]$ acts by $a \mapsto \iota(r) \cdot a$, where $\iota$
is the inversion of $R[G]$ and $\cdot$ is the original action on $A$.

As a bare type, the inversion twist of any type $A$ is a copy of $A$; the addition and the
action above are defined when $A$ is an $R[G]$-module. -/
@[ext]
structure InversionTwist (A : Type*) where
  of ::
  val : A

namespace InversionTwist

/-- **Underlying bijection of the inversion twist.** For every type $A$, the map sending an
element of the inversion twist of $A$ to its underlying element of $A$ is a bijection, whose
inverse sends $a \in A$ to its copy in the twist. -/
def equiv (A : Type*) : InversionTwist A ≃ A where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl

variable {R G} {A : Type*} [AddCommGroup A] [Module (MonoidAlgebra R G) A]

instance : AddCommGroup (InversionTwist A) := (equiv A).addCommGroup

instance : SMul (MonoidAlgebra R G) (InversionTwist A) where
  smul r a := of (inversion R G r • a.val)

/-- **Scalar action on the inversion twist.** Let $R$ be a commutative ring, $G$ a commutative
group and $A$ a module over the group ring $R[G]$. For every $r \in R[G]$ and every element $a$
of the inversion twist of $A$, with underlying element $\bar a \in A$, the underlying element of
$r \cdot a$ is $\iota(r) \cdot \bar a$, where $\iota$ is the inversion of $R[G]$ and $\cdot$ on
the right is the original action on $A$. -/
@[simp]
theorem val_smul (r : MonoidAlgebra R G) (a : InversionTwist A) :
    (r • a).val = inversion R G r • a.val := rfl

instance : Module (MonoidAlgebra R G) (InversionTwist A) where
  one_smul a := by
    ext
    change inversion R G 1 • a.val = a.val
    simp
  mul_smul r s a := by
    ext
    change inversion R G (r * s) • a.val = inversion R G r • inversion R G s • a.val
    simp [mul_smul]
  smul_zero r := by
    ext
    change inversion R G r • (0 : A) = 0
    simp
  smul_add r a b := by
    ext
    change inversion R G r • (a.val + b.val) =
      inversion R G r • a.val + inversion R G r • b.val
    simp
  zero_smul a := by
    ext
    change inversion R G 0 • a.val = 0
    simp
  add_smul r s a := by
    ext
    change inversion R G (r + s) • a.val =
      inversion R G r • a.val + inversion R G s • a.val
    simp [add_smul]

/-- **Twisting twice by inversion recovers the module.** Let $R$ be a commutative ring, $G$ a
commutative group and $A$ a module over the group ring $R[G]$. The map sending an element of the
inversion twist of the inversion twist of $A$ to its underlying element of $A$ is an
$R[G]$-linear isomorphism. -/
def twistTwistEquiv : InversionTwist (InversionTwist A) ≃ₗ[MonoidAlgebra R G] A where
  toFun a := a.val.val
  invFun a := of (of a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    change inversion R G (inversion R G r) • a.val.val = r • a.val.val
    rw [inversion_involution]

end InversionTwist

end GroupRing
