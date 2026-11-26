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

public import MathlibExt.Analysis.Normed.Operator.Arens
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Associative Arens products on the normed bidual

Over a nontrivially normed field `𝕜`, an associative bounded bilinear product on a seminormed
`𝕜`-space induces associative first and second Arens products on its continuous bidual.

For a nonunital seminormed ring `A` with compatible `𝕜`-scalar action, the products obey `‖p □
q‖≤‖p‖‖q‖` and `‖p ◇ q‖≤‖p‖‖q‖`. The first product makes `A**` a nonunital normed ring, with the
additive operations and iterated dual operator norm. Scalar multiplication is compatible with
both product factors.

If `𝕜` is complete, the bidual is complete; no completeness of `A` is required. A unit,
involution, equality of the two products and a C-star identity are separate properties.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

attribute [local instance]
  ContinuousLinearMap.arensDualSeminormed
  ContinuousLinearMap.arensDualNormedSpace
  ContinuousLinearMap.arensDualTargetSeminormed
  ContinuousLinearMap.arensDualTargetNormedSpace
  ContinuousLinearMap.arensDualTargetTopologicalAddGroup
  ContinuousLinearMap.arensMapSeminormed
  ContinuousLinearMap.arensMapNormedSpace
  ContinuousLinearMap.arensMapTopologicalAddGroup
  ContinuousLinearMap.arensBidualSeminormed
  ContinuousLinearMap.arensBidualNormedSpace
  ContinuousLinearMap.arensBidualMapSeminormed
  ContinuousLinearMap.arensBidualMapNormedSpace
  ContinuousLinearMap.arensBidualMapTopologicalAddGroup

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]

/-- **Definite norm on a continuous scalar dual.** Let `𝕜` be a nontrivially normed field. Let
`A` be a seminormed `𝕜`-space. the continuous dual `A*` is a normed additive commutative
group for the operator norm: `‖φ‖=0` forces `φ(a)=0` for every `a`, even when the seminorm
of `A` is not definite. -/
local instance arensAlgebraDualNormedGroup : NormedAddCommGroup (StrongDual 𝕜 A) :=
  NormedAddCommGroup.ofSeparation <| by
    intro phi hphi
    ext a
    apply norm_eq_zero.mp
    have hle : ‖phi a‖ ≤ 0 := by
      simpa only [hphi, zero_mul] using phi.le_opNorm a
    exact le_antisymm hle (norm_nonneg (phi a))

/-- **Associativity of the first Arens extension.** Let `𝕜` be a nontrivially normed field.
Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear map.
Write `A*`, `A**` for its continuous dual and bidual. assume `m(m(a,b),c)=m(a,m(b,c))` for
all `a,b,c ∈ A`. Then `m₁(m₁(p,q),r)=m₁(p,m₁(q,r))` for `p,q,r ∈ A**`, where
`m₁=m.arensFirst`. -/
theorem arensFirst_assoc (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b c, m (m a b) c = m a (m b c))
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (m.arensFirst p q) r = m.arensFirst p (m.arensFirst q r) := by
  ext phi
  change p (m.dualBilinear.dualBilinear q (m.dualBilinear.dualBilinear r phi)) =
    p (m.dualBilinear.dualBilinear (m.arensFirst q r) phi)
  apply congrArg p
  ext a
  change q (m.dualBilinear (m.dualBilinear.dualBilinear r phi) a) =
    q (m.dualBilinear.dualBilinear r (m.dualBilinear phi a))
  apply congrArg q
  ext b
  change r (m.dualBilinear phi (m a b)) =
    r (m.dualBilinear (m.dualBilinear phi a) b)
  apply congrArg r
  ext c
  change phi (m (m a b) c) = phi (m a (m b c))
  exact congrArg phi (h a b c)

/-- **Associativity of the second Arens extension.** Let `𝕜` be a nontrivially normed field.
Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear map.
Write `A*`, `A**` for its continuous dual and bidual. assume `m(m(a,b),c)=m(a,m(b,c))` for
all `a,b,c ∈ A`. Then `m₂(m₂(p,q),r)=m₂(p,m₂(q,r))` for `p,q,r ∈ A**`, where
`m₂=m.arensSecond`. -/
theorem arensSecond_assoc (m : A →L[𝕜] A →L[𝕜] A)
    (h : ∀ a b c, m (m a b) c = m a (m b c))
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (m.arensSecond p q) r = m.arensSecond p (m.arensSecond q r) := by
  have hflip : ∀ a b c, m.flip (m.flip a b) c = m.flip a (m.flip b c) := by
    intro a b c
    change m c (m b a) = m (m c b) a
    exact (h c b a).symm
  change m.flip.arensFirst r (m.flip.arensFirst q p) =
    m.flip.arensFirst (m.flip.arensFirst r q) p
  exact (arensFirst_assoc m.flip hflip r q p).symm

/-- **First Arens extension distributes in its first factor.** Let `𝕜` be a nontrivially
normed field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded
bilinear map. Write `A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst`
and `p,q,r ∈ A**`, `m₁(p+q,r)=m₁(p,r)+m₁(q,r)`. -/
theorem arensFirst_add_left (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (p + q) r = m.arensFirst p r + m.arensFirst q r :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L r) (m.arensFirst.map_add p q)

/-- **First Arens extension distributes in its second factor.** Let `𝕜` be a nontrivially
normed field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded
bilinear map. Write `A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst`
and `p,q,r ∈ A**`, `m₁(p,q+r)=m₁(p,q)+m₁(p,r)`. -/
theorem arensFirst_add_right (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst p (q + r) = m.arensFirst p q + m.arensFirst p r :=
  (m.arensFirst p).map_add q r

/-- **Zero first argument of the first Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst` and `q ∈
A**`, `m₁(0,q)=0`. -/
theorem arensFirst_zero_left (m : A →L[𝕜] A →L[𝕜] A)
    (q : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensFirst 0 q = 0 := by
  ext phi
  rfl

/-- **Zero second argument of the first Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst` and `p ∈
A**`, `m₁(p,0)=0`. -/
theorem arensFirst_zero_right (m : A →L[𝕜] A →L[𝕜] A)
    (p : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensFirst p 0 = 0 :=
  (m.arensFirst p).map_zero

/-- **Scalar action in the first Arens factor.** Let `𝕜` be a nontrivially normed field. Let
`A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear map. Write
`A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst`, `c : 𝕜` and `p,q ∈
A**`, `m₁(c • p,q)=c • m₁(p,q)`. -/
theorem arensFirst_smul_left (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst (c • p) q = c • m.arensFirst p q :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) (m.arensFirst.map_smul c p)

/-- **Scalar action in the second first-Arens factor.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₁=m.arensFirst`, `c : 𝕜`
and `p,q ∈ A**`, `m₁(p,c • q)=c • m₁(p,q)`. -/
theorem arensFirst_smul_right (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensFirst p (c • q) = c • m.arensFirst p q :=
  (m.arensFirst p).map_smul c q

/-- **Second Arens extension distributes in its first factor.** Let `𝕜` be a nontrivially
normed field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded
bilinear map. Write `A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond`
and `p,q,r ∈ A**`, `m₂(p+q,r)=m₂(p,r)+m₂(q,r)`. -/
theorem arensSecond_add_left (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (p + q) r = m.arensSecond p r + m.arensSecond q r :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L r) (m.arensSecond.map_add p q)

/-- **Second Arens extension distributes in its second factor.** Let `𝕜` be a nontrivially
normed field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded
bilinear map. Write `A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond`
and `p,q,r ∈ A**`, `m₂(p,q+r)=m₂(p,q)+m₂(p,r)`. -/
theorem arensSecond_add_right (m : A →L[𝕜] A →L[𝕜] A)
    (p q r : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond p (q + r) = m.arensSecond p q + m.arensSecond p r :=
  (m.arensSecond p).map_add q r

/-- **Zero first argument of the second Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond` and `q ∈
A**`, `m₂(0,q)=0`. -/
theorem arensSecond_zero_left (m : A →L[𝕜] A →L[𝕜] A)
    (q : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensSecond 0 q = 0 :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) m.arensSecond.map_zero

/-- **Zero second argument of the second Arens extension.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond` and `p ∈
A**`, `m₂(p,0)=0`. -/
theorem arensSecond_zero_right (m : A →L[𝕜] A →L[𝕜] A)
    (p : StrongDual 𝕜 (StrongDual 𝕜 A)) : m.arensSecond p 0 = 0 := by
  ext phi
  rfl

/-- **Scalar action in the first second-Arens factor.** Let `𝕜` be a nontrivially normed
field. Let `A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear
map. Write `A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond`, `c : 𝕜`
and `p,q ∈ A**`, `m₂(c • p,q)=c • m₂(p,q)`. -/
theorem arensSecond_smul_left (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond (c • p) q = c • m.arensSecond p q :=
  congrArg (fun L : StrongDual 𝕜 (StrongDual 𝕜 A) →L[𝕜]
    StrongDual 𝕜 (StrongDual 𝕜 A) => L q) (m.arensSecond.map_smul c p)

/-- **Scalar action in the second Arens factor.** Let `𝕜` be a nontrivially normed field. Let
`A` be a seminormed `𝕜`-space and `m : A →L[𝕜] A →L[𝕜] A` a bounded bilinear map. Write
`A*`, `A**` for its continuous dual and bidual. for `m₂=m.arensSecond`, `c : 𝕜` and `p,q ∈
A**`, `m₂(p,c • q)=c • m₂(p,q)`. -/
theorem arensSecond_smul_right (m : A →L[𝕜] A →L[𝕜] A) (c : 𝕜)
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    m.arensSecond p (c • q) = c • m.arensSecond p q :=
  (m.arensSecond p).map_smul c q

end ContinuousLinearMap

attribute [local instance] ContinuousLinearMap.arensAlgebraDualNormedGroup

namespace NormedSpace

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]
variable (A : Type v) [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- **Submultiplicative bound for the first Arens product.** Let `𝕜` be a nontrivially normed
field. Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action
satisfies `c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its
iterated operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. for
every `p,q ∈ A**`, `‖p □ q‖≤‖p‖*‖q‖`. -/
theorem firstArens_mul_norm_le (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖(ContinuousLinearMap.mul 𝕜 A).arensFirst p q‖ ≤ ‖p‖ * ‖q‖ := by
  calc
    ‖(ContinuousLinearMap.mul 𝕜 A).arensFirst p q‖ ≤
        ‖ContinuousLinearMap.mul 𝕜 A‖ * ‖p‖ * ‖q‖ :=
      (ContinuousLinearMap.mul 𝕜 A).norm_arensFirst_apply_le p q
    _ ≤ 1 * ‖p‖ * ‖q‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le 𝕜 A
    _ = ‖p‖ * ‖q‖ := by rw [one_mul]

/-- **Submultiplicative bound for the second Arens product.** Let `𝕜` be a nontrivially normed
field. Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action
satisfies `c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its
iterated operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. for
every `p,q ∈ A**`, `‖p ◇ q‖≤‖p‖*‖q‖`. -/
theorem secondArens_mul_norm_le (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖(ContinuousLinearMap.mul 𝕜 A).arensSecond p q‖ ≤ ‖p‖ * ‖q‖ := by
  calc
    ‖(ContinuousLinearMap.mul 𝕜 A).arensSecond p q‖ ≤
        ‖ContinuousLinearMap.mul 𝕜 A‖ * ‖p‖ * ‖q‖ :=
      (ContinuousLinearMap.mul 𝕜 A).norm_arensSecond_apply_le p q
    _ ≤ 1 * ‖p‖ * ‖q‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le 𝕜 A
    _ = ‖p‖ * ‖q‖ := by rw [one_mul]

/-- **Nonunital bidual ring with the first Arens product.** Let `𝕜` be a nontrivially normed
field. Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action
satisfies `c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its
iterated operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products.
`firstArensNonUnitalRing 𝕜 A` gives `A**` multiplication `p*q=p □ q` and its
continuous-dual addition, zero and negation. -/
@[instance_reducible] noncomputable def firstArensNonUnitalRing :
    NonUnitalRing (StrongDual 𝕜 (StrongDual 𝕜 A)) where
  __ := (inferInstance : AddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 A)))
  mul := fun p q => (ContinuousLinearMap.mul 𝕜 A).arensFirst p q
  mul_assoc := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_assoc
    (fun a b c => mul_assoc a b c) p q r
  left_distrib := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_add_right p q r
  right_distrib := fun p q r => (ContinuousLinearMap.mul 𝕜 A).arensFirst_add_left p q r
  zero_mul := (ContinuousLinearMap.mul 𝕜 A).arensFirst_zero_left
  mul_zero := (ContinuousLinearMap.mul 𝕜 A).arensFirst_zero_right

/-- **Normed ring of the first Arens bidual.** Let `𝕜` be a nontrivially normed field. Let `A`
be a nonunital seminormed ring and normed `𝕜`-space whose scalar action satisfies `c •
(a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its iterated
operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products.
`firstArensNonUnitalNormedRing 𝕜 A` equips `A**` with `p*q=p □ q` and the iterated
operator norm, satisfying `‖p*q‖≤‖p‖‖q‖`. -/
@[instance_reducible] noncomputable def firstArensNonUnitalNormedRing :
    NonUnitalNormedRing (StrongDual 𝕜 (StrongDual 𝕜 A)) where
  __ := firstArensNonUnitalRing 𝕜 A
  __ := (inferInstance : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 A)))
  dist_eq := fun p q => dist_eq_norm_neg_add p q
  norm_mul_le := firstArens_mul_norm_le 𝕜 A

/-- **Multiplication in the first Arens normed ring.** Let `𝕜` be a nontrivially normed field.
Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action satisfies
`c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its iterated
operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. the product
in `firstArensNonUnitalNormedRing 𝕜 A` is `p*q=(ContinuousLinearMap.mul 𝕜 A).arensFirst p
q` for `p,q ∈ A**`. -/
theorem firstArensNonUnitalNormedRing_mul
    (p q : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    p * q = (ContinuousLinearMap.mul 𝕜 A).arensFirst p q := rfl

/-- **Dual operator norm of the first Arens ring.** Let `𝕜` be a nontrivially normed field.
Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action satisfies
`c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its iterated
operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. for `p ∈
A**`, the norm in the first Arens normed ring is its continuous-bidual operator norm
`‖p‖=inf {C ≥ 0 : ∀ φ ∈ A*, ‖p(φ)‖≤C‖φ‖}`. -/
theorem firstArensNonUnitalNormedRing_norm (p : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    (firstArensNonUnitalNormedRing 𝕜 A).toNorm.norm p = ‖p‖ := rfl

/-- **Scalar tower law for the first Arens product.** Let `𝕜` be a nontrivially normed field.
Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action satisfies
`c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its iterated
operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. for `c : 𝕜`
and `p,q ∈ A**`, `(c • p) □ q=c • (p □ q)`. -/
theorem firstArensIsScalarTower :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    IsScalarTower 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 A)) (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  let _ := firstArensNonUnitalNormedRing 𝕜 A
  refine ⟨?_⟩
  intro c p q
  exact (ContinuousLinearMap.mul 𝕜 A).arensFirst_smul_left c p q

/-- **Commuting scalar action in the second Arens factor.** Let `𝕜` be a nontrivially normed
field. Let `A` be a nonunital seminormed ring and normed `𝕜`-space whose scalar action
satisfies `c • (a*b)=(c • a)*b=a*(c • b)`. Write `A**` for the continuous bidual with its
iterated operator norm, and `p □ q`, `p ◇ q` for the first and second Arens products. for
`c : 𝕜` and `p,q ∈ A**`, `p □ (c • q)=c • (p □ q)`. -/
theorem firstArensSMulCommClass :
    letI := firstArensNonUnitalNormedRing 𝕜 A
    SMulCommClass 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 A)) (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  let _ := firstArensNonUnitalNormedRing 𝕜 A
  refine ⟨?_⟩
  intro c p q
  exact ((ContinuousLinearMap.mul 𝕜 A).arensFirst_smul_right c p q).symm

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- **Completeness of the continuous bidual.** Let `𝕜` be a nontrivially normed field. Assume
`𝕜` is complete and `A` is a nonunital seminormed ring and normed `𝕜`-space. `A**` is
complete in its iterated operator norm; neither completeness of `A` nor scalar
compatibility with its ring product is required for this completeness statement. -/
theorem firstArensCompleteSpace [CompleteSpace 𝕜] :
    CompleteSpace (StrongDual 𝕜 (StrongDual 𝕜 A)) := by
  infer_instance

end NormedSpace
