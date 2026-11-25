/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.Projection
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGrading
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Coalgebra
import Mathlib.Tactic.Abel

/-!
# Homogeneous components of the Chevalley–Eilenberg coproduct

Alternating descent and homogeneous projections construct the coproduct
components. In every source degree and bidegree, the boundary satisfies the
two-term coderivation equation with Koszul sign `(-1)^p`. The components
vanish off the source antidiagonal, recover the coproduct by a finite sum,
and are natural under Lie algebra homomorphisms.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "E" => ExteriorAlgebra R L
local notation "Δ" => ExteriorAlgebra.coproduct R L
local notation "π" => exteriorPower.projection R L

/-- Canonical homogeneous projections intertwine the degree-lowering boundary. -/
theorem projection_boundary (p : ℕ) (a : E) :
    π p (boundary R L a) = differential R L p (π (p + 1) a) := by
  have h : (π p).comp (boundary R L) = (differential R L p).comp (π (p + 1)) := by
    apply ExteriorAlgebra.lhom_ext
    intro k
    apply AlternatingMap.ext
    intro v
    cases k with
    | zero =>
        have hzero : (0 : ℕ) ≠ p + 1 := fun hzero => Nat.succ_ne_zero p hzero.symm
        change π p (boundary R L (ExteriorAlgebra.ιMulti R 0 v)) =
          differential R L p (π (p + 1) (ExteriorAlgebra.ιMulti R 0 v))
        rw [exteriorPower.projection_ιMulti_ne R L (p + 1) 0 hzero,
          map_zero, ExteriorAlgebra.ιMulti_zero_apply, boundary_one, map_zero]
    | succ k =>
        change π p (boundary R L (ExteriorAlgebra.ιMulti R (k + 1) v)) =
          differential R L p (π (p + 1) (ExteriorAlgebra.ιMulti R (k + 1) v))
        by_cases hk : k = p
        · subst k
          rw [exteriorPower.projection_ιMulti_self]
          change π p (differential R L p (exteriorPower.ιMulti R (p + 1) v) : E) =
            differential R L p (exteriorPower.ιMulti R (p + 1) v)
          exact exteriorPower.projection_subtype_apply R L p _
        · have hsucc : k + 1 ≠ p + 1 := fun hsucc => hk (Nat.succ.inj hsucc)
          rw [exteriorPower.projection_ιMulti_ne R L (p + 1) (k + 1) hsucc, map_zero]
          apply exteriorPower.projection_eq_zero_of_mem R L p k hk
          simpa only [Nat.add_sub_cancel] using boundary_mem_exteriorPower R L (k + 1)
            (ExteriorAlgebra.ιMulti R (k + 1) v)
            (ExteriorAlgebra.ιMulti_range R (k + 1) ⟨v, rfl⟩)
  exact LinearMap.congr_fun h a

/-- The ambient tensor differential gives the homogeneous Koszul sign. -/
theorem tensorBoundary_projection (p q : ℕ) (t : E ⊗[R] E) :
    TensorProduct.map (π p) (π q) (tensorBoundary R L t) =
      (differential R L p).rTensor (⋀[R]^q L)
          (TensorProduct.map (π (p + 1)) (π q) t) +
        (-1 : R) ^ p • (differential R L q).lTensor (⋀[R]^p L)
          (TensorProduct.map (π p) (π (q + 1)) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [tensorBoundary_tmul, map_add, TensorProduct.map_tmul,
        projection_boundary, exteriorPower.projection_involute,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.smul_tmul']
  | add t s ht hs =>
      simp only [map_add, ht, hs, smul_add]
      abel

/-- The alternating source of a coproduct component. -/
def coproductComponentAlternating (n p q : ℕ) :
    L [⋀^Fin n]→ₗ[R] ((⋀[R]^p L) ⊗[R] (⋀[R]^q L)) :=
  ((TensorProduct.map (π p) (π q)).comp Δ).compAlternatingMap
    (ExteriorAlgebra.ιMulti R n)

/-- The degree-`n`, bidegree-`(p,q)` coproduct component, by alternating descent. -/
def coproductComponent (n p q : ℕ) :
    (⋀[R]^n L) →ₗ[R] ((⋀[R]^p L) ⊗[R] (⋀[R]^q L)) :=
  exteriorPower.alternatingMapLinearEquiv (R := R) (n := n) (M := L)
    (N := ((⋀[R]^p L) ⊗[R] (⋀[R]^q L))) (coproductComponentAlternating R L n p q)

/-- Its characteristic equation uses the ambient coproduct and degree projections. -/
theorem coproductComponent_apply (n p q : ℕ) (a : ⋀[R]^n L) :
    coproductComponent R L n p q a = TensorProduct.map (π p) (π q) (Δ (a : E)) := by
  have h : coproductComponent R L n p q =
      (TensorProduct.map (π p) (π q)).comp ((ExteriorAlgebra.coproduct R L).comp (⋀[R]^n L).subtype) := by
    apply exteriorPower.linearMap_ext (R := R) (n := n) (M := L)
      (N := ((⋀[R]^p L) ⊗[R] (⋀[R]^q L)))
    apply AlternatingMap.ext
    intro v
    simp only [coproductComponent, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      coproductComponentAlternating, LinearMap.compAlternatingMap_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe]
  exact LinearMap.congr_fun h a

/-- The homogeneous CE coderivation law, without arithmetic casts between source degrees. -/
theorem coproductComponent_boundary (n p q : ℕ) :
    (coproductComponent R L n p q).comp (differential R L n) =
      ((differential R L p).rTensor (⋀[R]^q L)).comp
          (coproductComponent R L (n + 1) (p + 1) q) +
        (-1 : R) ^ p • ((differential R L q).lTensor (⋀[R]^p L)).comp
          (coproductComponent R L (n + 1) p (q + 1)) := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    coproductComponent_apply]
  rw [differential_coe, coproduct_boundary, tensorBoundary_projection]

/-- The coproduct component vanishes off its source antidiagonal. -/
theorem coproductComponent_eq_zero_of_ne (n p q : ℕ) (hpq : p + q ≠ n) :
    coproductComponent R L n p q = 0 := by
  apply LinearMap.ext
  intro a
  rw [coproductComponent_apply]
  exact ExteriorAlgebra.projection_tensor_eq_zero_of_mem_degree R L n p q hpq _
    (ExteriorAlgebra.coproduct_mem_degree R L n a a.property)

/-- The degree-`n` coproduct is recovered from its finite component family. -/
theorem coproduct_eq_sum_components (n : ℕ) (a : ⋀[R]^n L) :
    Δ (a : E) = ∑ p : Fin (n + 1),
      TensorProduct.map (⋀[R]^p.val L).subtype (⋀[R]^(n - p.val) L).subtype
        (coproductComponent R L n p.val (n - p.val) a) := by
  symm
  simpa only [ExteriorAlgebra.degreeTensorReconstruction, LinearMap.sum_apply,
    LinearMap.comp_apply, coproductComponent_apply] using
    ExteriorAlgebra.coproduct_degreeTensorReconstruction R L n a

section Naturality

variable {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- coproduct components are natural under Lie algebra maps. -/
theorem coproductComponent_naturality (n p q : ℕ) (f : L →ₗ⁅R⁆ L') :
    (coproductComponent R L' n p q).comp (exteriorPower.map n f.toLinearMap) =
      (TensorProduct.map (exteriorPower.map p f.toLinearMap)
        (exteriorPower.map q f.toLinearMap)).comp (coproductComponent R L n p q) := by
  have hproj (k : ℕ) (a : E) :
      exteriorPower.projection R L' k (ExteriorAlgebra.map f.toLinearMap a) =
        exteriorPower.map k f.toLinearMap (π k a) :=
    LinearMap.congr_fun (exteriorPower.projection_naturality R L k f.toLinearMap) a
  have htensor (t : E ⊗[R] E) :
      TensorProduct.map (exteriorPower.projection R L' p) (exteriorPower.projection R L' q)
          (TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap
            (ExteriorAlgebra.map f.toLinearMap).toLinearMap t) =
        TensorProduct.map (exteriorPower.map p f.toLinearMap) (exteriorPower.map q f.toLinearMap)
          (TensorProduct.map (π p) (π q) t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hproj]
    | add t s ht hs => simp only [map_add, ht, hs]
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, coproductComponent_apply, exteriorPower.coe_map]
  rw [← ExteriorAlgebra.coproduct_naturality R L f.toLinearMap]
  exact htensor (Δ (a : E))

end Naturality

end ChevalleyEilenberg
