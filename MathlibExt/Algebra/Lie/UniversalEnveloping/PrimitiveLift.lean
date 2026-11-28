/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.BialgebraNaturality
public import MathlibExt.Algebra.Lie.UniversalEnveloping.HopfAlgebra
public import MathlibExt.RingTheory.HopfAlgebra.Hom

/-!
# Primitive-valued maps and enveloping bialgebra morphisms

Let R be commutative, L an R-Lie algebra and A an R-bialgebra whose underlying algebra is a
ring. A Lie map f : L → P_R(A) into its primitive Lie algebra extends uniquely to a bialgebra
map U_R(L) → A. The extension sends ι_R(x) to f(x), and restriction of a bialgebra map
evaluates it on the canonical primitive generators.

This gives a set equivalence between primitive-valued Lie maps and enveloping bialgebra maps,
natural in both variables. Its counit ε_A : U_R(P_R(A)) → A sends a primitive generator to its
underlying value. With η_L : L → P_R(U_R(L)), the identities P(ε_A) ∘ η_{P(A)} = id and
ε_{U(L)} ∘ U(η_L) = id hold. For a Hopf target, every such lift commutes with the antipodes.
Scalar, Lie and target algebra universes are independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v v' w w'

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

section Lift

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {A : Type w} [Ring A] [Bialgebra R A]
  {B : Type w'} [Ring B] [Bialgebra R B]

private theorem liftPrimitive_counit
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    (Bialgebra.counitAlgHom R A).comp
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f)) =
      Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Coalgebra.counit (R := R)
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x)) =
    Coalgebra.counit (R := R) (ι R x)
  rw [lift_ι_apply, counit_ι]
  exact ((Bialgebra.mem_primitiveLieSubalgebra R A).mp (f x).property).counit_eq_zero

private theorem liftPrimitive_comul
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    (Algebra.TensorProduct.map
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))).comp
        (Bialgebra.comulAlgHom R (UniversalEnvelopingAlgebra R L)) =
      (Bialgebra.comulAlgHom R A).comp
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f)) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.map
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
      (Coalgebra.comul (R := R) (ι R x)) =
    Coalgebra.comul (R := R)
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x))
  rw [comul_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, map_one, lift_ι_apply]
  exact ((Bialgebra.mem_primitiveLieSubalgebra R A).mp
    (f x).property).comul_eq_tmul_add_tmul.symm

/-- Bialgebra extension of a primitive-valued Lie morphism.

For f : L →ₗ⁅R⁆ P_R(A), with R commutative and A an R-bialgebra ring, extend the composite L →
A by the enveloping algebra universal property. Primitivity makes this algebra lift preserve
both counit and comultiplication, giving U_R(L) →ₐc[R] A. -/
def liftPrimitive (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    UniversalEnvelopingAlgebra R L →ₐc[R] A :=
  BialgHom.ofAlgHom
    (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
    (by exact liftPrimitive_counit R f)
    (by exact liftPrimitive_comul R f)

/-- Generator value of a primitive bialgebra lift.

For a Lie map f : L → P_R(A), its bialgebra extension satisfies liftPrimitive R f (ι_R(x)) =
f(x), viewed in A. -/
@[simp]
theorem liftPrimitive_ι (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) (x : L) :
    liftPrimitive R f (ι R x) = (f x : A) := by
  change lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x) = _
  rw [lift_ι_apply]
  rfl

/-- Primitive restriction of an enveloping bialgebra map.

For g : U_R(L) →ₐc[R] A, compose the canonical primitive generator map η_L : L → P_R(U_R(L))
with the Lie map on primitives induced by g. This gives L →ₗ⁅R⁆ P_R(A). -/
def restrictPrimitive (g : UniversalEnvelopingAlgebra R L →ₐc[R] A) :
    L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A :=
  g.primitiveLieMap.comp (ιPrimitive R L)

/-- Hom equivalence for primitive-valued enveloping maps.

For an R-Lie algebra L and R-bialgebra ring A, primitive extension and restriction give (L
→ₗ⁅R⁆ P_R(A)) ≃ (U_R(L) →ₐc[R] A). The equivalence sends f to its enveloping bialgebra lift
and g to its value on primitive generators. -/
def liftPrimitiveEquiv (L : Type v) [LieRing L] [LieAlgebra R L]
    (A : Type w) [Ring A] [Bialgebra R A] :
    (L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) ≃
      (UniversalEnvelopingAlgebra R L →ₐc[R] A) where
  toFun := liftPrimitive R
  invFun := restrictPrimitive R
  left_inv f := by
    apply LieHom.ext
    intro x
    apply Subtype.ext
    change liftPrimitive R f (ι R x) = (f x : A)
    exact liftPrimitive_ι R f x
  right_inv g := by
    have h : (liftPrimitive R (restrictPrimitive R g)).toAlgHom = g.toAlgHom := by
      apply hom_ext
      apply LieHom.ext
      intro x
      change liftPrimitive R (restrictPrimitive R g) (ι R x) = g (ι R x)
      rw [liftPrimitive_ι]
      rfl
    apply BialgHom.ext
    intro a
    exact AlgHom.congr_fun h a

/-- Source naturality of primitive enveloping lifts.

For Lie maps g : L → L' and f : L' → P_R(A), the lifts satisfy liftPrimitive(f ∘ g) =
liftPrimitive(f) ∘ U_R(g), where U_R(g) is the canonical enveloping bialgebra map. -/
theorem liftPrimitive_comp_map (g : L →ₗ⁅R⁆ L')
    (f : L' →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    liftPrimitive R (f.comp g) = (liftPrimitive R f).comp (mapBialgHom R g) := by
  have h : (liftPrimitive R (f.comp g)).toAlgHom =
      ((liftPrimitive R f).comp (mapBialgHom R g)).toAlgHom := by
    apply hom_ext
    apply LieHom.ext
    intro x
    change liftPrimitive R (f.comp g) (ι R x) = liftPrimitive R f (map R g (ι R x))
    rw [liftPrimitive_ι, map_ι, liftPrimitive_ι]
    rfl
  apply BialgHom.ext
  intro a
  exact AlgHom.congr_fun h a

/-- Target naturality of primitive enveloping lifts.

For a bialgebra map g : A → B and Lie map f : L → P_R(A), g ∘ liftPrimitive(f) =
liftPrimitive(P_R(g) ∘ f). -/
theorem comp_liftPrimitive (g : A →ₐc[R] B)
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    g.comp (liftPrimitive R f) = liftPrimitive R (g.primitiveLieMap.comp f) := by
  have h : (g.comp (liftPrimitive R f)).toAlgHom =
      (liftPrimitive R (g.primitiveLieMap.comp f)).toAlgHom := by
    apply hom_ext
    apply LieHom.ext
    intro x
    change g (liftPrimitive R f (ι R x)) =
      liftPrimitive R (g.primitiveLieMap.comp f) (ι R x)
    rw [liftPrimitive_ι, liftPrimitive_ι]
    rfl
  apply BialgHom.ext
  intro a
  exact AlgHom.congr_fun h a

end Lift

section Counit

variable (A : Type w) [Ring A] [Bialgebra R A]

/-- Counit map from the enveloping algebra of primitives.

For an R-bialgebra ring A, extend the identity Lie map of P_R(A) to the bialgebra morphism ε_A
: U_R(P_R(A)) → A. It sends each primitive generator to the underlying element of A. -/
def primitiveCounit :
    UniversalEnvelopingAlgebra R (Bialgebra.primitiveLieSubalgebra R A) →ₐc[R] A :=
  liftPrimitive R (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
    Bialgebra.primitiveLieSubalgebra R A)

/-- Generator value of the primitive counit.

For x ∈ P_R(A), the bialgebra counit map ε_A satisfies ε_A(ι_R(x)) = x, viewed in A. -/
@[simp]
theorem primitiveCounit_ι (x : Bialgebra.primitiveLieSubalgebra R A) :
    primitiveCounit R A (ι R x) = (x : A) := by
  exact liftPrimitive_ι R (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
    Bialgebra.primitiveLieSubalgebra R A) x

/-- Primitive triangle identity for the counit.

For an R-bialgebra ring A, the Lie map on primitives induced by ε_A : U_R(P_R(A)) → A,
composed with η_{P(A)}, is the identity of P_R(A). -/
theorem primitiveCounit_primitiveLieMap :
    (primitiveCounit R A).primitiveLieMap.comp
        (ιPrimitive R (Bialgebra.primitiveLieSubalgebra R A)) =
      (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R A) := by
  exact (liftPrimitiveEquiv R (Bialgebra.primitiveLieSubalgebra R A) A).left_inv LieHom.id

variable {A} {B : Type w'} [Ring B] [Bialgebra R B]

/-- Naturality of primitive counit maps.

For a bialgebra homomorphism g : A → B over R, g ∘ ε_A = ε_B ∘ U_R(P_R(g)), where ε is the map
extending the primitive inclusion. -/
theorem primitiveCounit_naturality (g : A →ₐc[R] B) :
    g.comp (primitiveCounit R A) =
      (primitiveCounit R B).comp (mapBialgHom R g.primitiveLieMap) := by
  apply BialgHom.ext
  intro a
  change g (lift R (Bialgebra.primitiveLieSubalgebra R A).incl a) =
    lift R (Bialgebra.primitiveLieSubalgebra R B).incl (map R g.primitiveLieMap a)
  exact AlgHom.congr_fun g.primitive_enveloping_naturality a

end Counit

section Triangle

variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Enveloping triangle identity for primitive generators.

For an R-Lie algebra L, the composite U_R(L) → U_R(P_R(U_R(L))) → U_R(L), using U_R(η_L) and
ε_{U_R(L)}, is the identity bialgebra map. -/
theorem primitiveCounit_comp_map_ιPrimitive :
    (primitiveCounit R (UniversalEnvelopingAlgebra R L)).comp
        (mapBialgHom R (ιPrimitive R L)) =
      BialgHom.id R (UniversalEnvelopingAlgebra R L) := by
  change (liftPrimitive R (LieHom.id :
      Bialgebra.primitiveLieSubalgebra R (UniversalEnvelopingAlgebra R L) →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R (UniversalEnvelopingAlgebra R L))).comp
      (mapBialgHom R (ιPrimitive R L)) = _
  rw [← liftPrimitive_comp_map, LieHom.id_comp]
  have h := (liftPrimitiveEquiv R L (UniversalEnvelopingAlgebra R L)).right_inv
    (BialgHom.id R (UniversalEnvelopingAlgebra R L))
  change liftPrimitive R (restrictPrimitive R (BialgHom.id R
    (UniversalEnvelopingAlgebra R L))) = BialgHom.id R (UniversalEnvelopingAlgebra R L) at h
  simpa only [restrictPrimitive, BialgHom.primitiveLieMap_id, LieHom.id_comp] using! h

end Triangle

section Hopf

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {A : Type w} [Ring A] [HopfAlgebra R A]

/-- Antipode compatibility of a primitive-valued lift.

For a Hopf R-algebra A and Lie map f : L → P_R(A), the bialgebra lift satisfies
liftPrimitive(f)(S_{U_R(L)}(a)) = S_A(liftPrimitive(f)(a)) for every a ∈ U_R(L). -/
theorem liftPrimitive_antipode (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A)
    (a : UniversalEnvelopingAlgebra R L) :
    liftPrimitive R f (HopfAlgebra.antipode R a) =
      HopfAlgebra.antipode R (liftPrimitive R f a) := by
  exact (liftPrimitive R f).map_antipode a

end Hopf

end UniversalEnvelopingAlgebra
