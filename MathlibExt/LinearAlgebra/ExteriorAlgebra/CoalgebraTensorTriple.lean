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

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraTensorDegree

/-!
# Triple tensor degrees and exterior coassociativity

Let R be a commutative ring, M an R-module, Eₙ=∧ⁿ_RM and Tₙ=⊕_{p+q=n}Eₚ⊗_RE_q. The
right-associated triple degree is ⊕_{p+s=n}Eₚ⊗T_s; the left-associated degree is
⊕_{s+r=n}T_s⊗E_r. Their pure components are indexed by p+q+r=n.

Both degrees realize in E⊗(E⊗E), where E=ExteriorAlgebra(R,M); left realization includes the
ordinary associator. Right realization has a finite projection lift as a left inverse. The
graded associator agrees with these realizations and introduces no permutation sign.

Applying the graded coproduct to the left or right tensor factor gives the two iterated
coproduct maps. Their equality after the associator proves coassociativity in every n : ℕ. R and
M retain their separate universes, with the categorical module universe max(u,v); no flatness
assumption is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "P" => E ⊗[R] E
local notation "𝓔" => gradedExterior R M
local notation "𝓣" => gradedTensorSquare R M
local notation "π" => exteriorPower.projection R M

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. tripleRightDegree in degree n is ⊕_{p+s=n} Eₚ⊗_RT_s, equivalently the
right-associated sum of Eₚ⊗(E_q⊗E_r) over p+q+r=n. -/
def tripleRightDegree (n : ℕ) : (ModuleCat.{max u v} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorObj 𝓔 𝓣 n

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. tripleLeftDegree in degree n is ⊕_{s+r=n} T_s⊗_RE_r, equivalently the
left-associated sum of (Eₚ⊗E_q)⊗E_r over p+q+r=n. -/
def tripleLeftDegree (n : ℕ) : (ModuleCat.{max u v} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorObj 𝓣 𝓔 n

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For p,q,n : ℕ with p+q=n, tripleRightOuterι is the coproduct inclusion Eₚ⊗_RT_q →
tripleRightDegree n. -/
def tripleRightOuterι (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R ((⋀[R]^p M) ⊗[R] tensorDegree R M q) ⟶ tripleRightDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ιTensorObj 𝓔 𝓣 p q n h

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For p,q,n : ℕ with p+q=n, tripleLeftOuterι is the inclusion Tₚ⊗_RE_q →
tripleLeftDegree n. -/
def tripleLeftOuterι (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R (tensorDegree R M p ⊗[R] (⋀[R]^q M)) ⟶ tripleLeftDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ιTensorObj 𝓣 𝓔 p q n h

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. The right realization maps tripleRightDegree n into E⊗_R(E⊗_RE), using Eₚ ↪ E on the
first factor and the degree-q tensor realization on the second. A pure homogeneous a⊗(b⊗c)
retains these three factors. -/
def tripleRightRealize (n : ℕ) : tripleRightDegree R M n ⟶ ModuleCat.of R (E ⊗[R] P) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorObjDesc (fun p q _ =>
    ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (tensorDegreeRealize R M q).hom))

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. The left realization includes Tₚ⊗E_q into (E⊗E)⊗E and then applies the ordinary
tensor associator to E⊗(E⊗E). Thus (a⊗b)⊗c is realized as a⊗(b⊗c). -/
def tripleLeftRealize (n : ℕ) : tripleLeftDegree R M n ⟶ ModuleCat.of R (E ⊗[R] P) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorObjDesc (fun p q _ => ModuleCat.ofHom
    ((TensorProduct.assoc R E E E).toLinearMap.comp
      (TensorProduct.map (tensorDegreeRealize R M p).hom (⋀[R]^q M).subtype)))

@[reassoc]
theorem tripleRightOuterι_realize (p q n : ℕ) (h : p + q = n) :
    tripleRightOuterι R M p q n h ≫ tripleRightRealize R M n =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (tensorDegreeRealize R M q).hom) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ι_tensorObjDesc (X₁ := 𝓔) (X₂ := 𝓣) _ p q h

@[reassoc]
theorem tripleLeftOuterι_realize (p q n : ℕ) (h : p + q = n) :
    tripleLeftOuterι R M p q n h ≫ tripleLeftRealize R M n =
      ModuleCat.ofHom ((TensorProduct.assoc R E E E).toLinearMap.comp
        (TensorProduct.map (tensorDegreeRealize R M p).hom (⋀[R]^q M).subtype)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ι_tensorObjDesc (X₁ := 𝓣) (X₂ := 𝓔) _ p q h

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For n : ℕ, tripleRightLift maps E⊗(E⊗E) to tripleRightDegree n by ∑_{p=0}ⁿ ι_{p,n-p}
∘ (πₚ⊗L_{n-p}), where πₚ is the exterior projection and L_s the tensor-degree lift. -/
def tripleRightLift (n : ℕ) : ModuleCat.of R (E ⊗[R] P) ⟶ tripleRightDegree R M n :=
  ∑ p : Fin (n + 1),
    ModuleCat.ofHom (TensorProduct.map (π p.val) (tensorDegreeLift R M (n - p.val)).hom) ≫
      tripleRightOuterι R M p.val (n - p.val) n
        (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For each n : ℕ, tripleRightRealize followed by tripleRightLift is the identity on
tripleRightDegree n. Hence right triple realization is a split injection, without a flatness
hypothesis. -/
theorem tripleRightRealize_lift (n : ℕ) :
    tripleRightRealize R M n ≫ tripleRightLift R M n = 𝟙 (tripleRightDegree R M n) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  change tripleRightOuterι R M i j n hij ≫ _ = tripleRightOuterι R M i j n hij ≫ 𝟙 _
  rw [tripleRightOuterι_realize_assoc]
  unfold tripleRightLift
  rw [Preadditive.comp_sum]
  have hi : i < n + 1 := Nat.lt_succ_of_le (Nat.le.intro hij)
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hni : n - p.val = j := by change n - i = j; rw [← hij, Nat.add_sub_cancel_left]
  rw [Finset.sum_eq_single p]
  · have hmaps : (TensorProduct.map (π i) (tensorDegreeLift R M j).hom).comp
        (TensorProduct.map (⋀[R]^i M).subtype (tensorDegreeRealize R M j).hom) = LinearMap.id := by
      apply TensorProduct.ext'
      intro a t
      have ht := congrArg (fun f => f.hom t) (tensorDegreeRealize_lift R M j)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] at ht
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_subtype_apply, LinearMap.id_apply]
      rw [ht]
    subst j
    have hc : ModuleCat.ofHom (TensorProduct.map (⋀[R]^i M).subtype
        (tensorDegreeRealize R M (n - p.val)).hom) ≫
        ModuleCat.ofHom (TensorProduct.map (π i) (tensorDegreeLift R M (n - p.val)).hom) =
        𝟙 (ModuleCat.of R ((⋀[R]^i M) ⊗[R] tensorDegree R M (n - p.val))) := by
      apply ModuleCat.hom_ext
      exact hmaps
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ tripleRightOuterι R M i (n - p.val) n hij) hc).trans
        (Category.id_comp _))
  · intro q hq hqp
    have hiq : i ≠ q.val := fun hiq => hqp (Fin.ext hiq.symm)
    have hmaps : (TensorProduct.map (π q.val) (tensorDegreeLift R M (n - q.val)).hom).comp
        (TensorProduct.map (⋀[R]^i M).subtype (tensorDegreeRealize R M j).hom) = 0 := by
      apply TensorProduct.ext'
      intro a t
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_eq_zero_of_mem R M q.val i hiq a a.property,
        TensorProduct.zero_tmul, LinearMap.zero_apply]
    rw [← Category.assoc, ← ModuleCat.ofHom_comp, hmaps, ModuleCat.ofHom_zero,
      zero_comp]
  · intro hp
    exact False.elim (hp (Finset.mem_univ p))

theorem tripleRightRealize_injective (n : ℕ) :
    Function.Injective (tripleRightRealize R M n).hom := by
  apply Function.LeftInverse.injective
  intro x
  exact congrArg (fun f => f.hom x) (tripleRightRealize_lift R M n)

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For p,q,r,n : ℕ with p+q+r=n, tripleRightι includes Eₚ⊗(E_q⊗E_r) into
tripleRightDegree n by first including E_q⊗E_r in T_{q+r}, then taking the outer
(p,q+r)-summand. -/
def tripleRightι (p q r n : ℕ) (h : p + q + r = n) :
    ModuleCat.of R ((⋀[R]^p M) ⊗[R] ((⋀[R]^q M) ⊗[R] (⋀[R]^r M))) ⟶
      tripleRightDegree R M n :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id (tensorDegreeι R M q r (q + r) rfl).hom) ≫
    tripleRightOuterι R M p (q + r) n (by rw [← Nat.add_assoc, h])

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For p,q : ℕ, the R-module tensor Eₚ⊗_RE_q carries its usual additive commutative
group structure, used in the left-associated triple tensor module. -/
local instance leftTensorAddGroup (p q : ℕ) :
    AddCommGroup (TensorProduct R (↥(⋀[R]^p M)) (↥(⋀[R]^q M))) :=
  TensorProduct.addCommGroup

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For p,q,r,n : ℕ with p+q+r=n, tripleLeftι includes (Eₚ⊗E_q)⊗E_r into
tripleLeftDegree n, first taking the (p,q)-summand of T_{p+q}, then the outer (p+q,r)-summand. -/
def tripleLeftι (p q r n : ℕ) (h : p + q + r = n) :
    ModuleCat.of R (TensorProduct R
      (TensorProduct R (↥(⋀[R]^p M)) (↥(⋀[R]^q M))) (↥(⋀[R]^r M))) ⟶
      tripleLeftDegree R M n :=
  ModuleCat.ofHom (TensorProduct.map (tensorDegreeι R M p q (p + q) rfl).hom
    (LinearMap.id : (⋀[R]^r M) →ₗ[R] (⋀[R]^r M))) ≫
    tripleLeftOuterι R M (p + q) r n h

@[reassoc]
theorem tripleRightι_realize (p q r n : ℕ) (h : p + q + r = n) :
    tripleRightι R M p q r n h ≫ tripleRightRealize R M n =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype
        (TensorProduct.map (⋀[R]^q M).subtype (⋀[R]^r M).subtype)) := by
  rw [tripleRightι, Category.assoc, tripleRightOuterι_realize]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a t
  have ht := congrArg (fun f => f.hom t) (tensorDegreeι_realize R M q r (q + r) rfl)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at ht
  change (a : E) ⊗ₜ[R] (tensorDegreeRealize R M (q + r)).hom
      ((tensorDegreeι R M q r (q + r) rfl).hom t) =
    (a : E) ⊗ₜ[R] TensorProduct.map (⋀[R]^q M).subtype (⋀[R]^r M).subtype t
  rw [ht]

@[reassoc]
theorem tripleLeftι_realize (p q r n : ℕ) (h : p + q + r = n) :
    tripleLeftι R M p q r n h ≫ tripleLeftRealize R M n =
      ModuleCat.ofHom ((TensorProduct.assoc R E E E).toLinearMap.comp
        (TensorProduct.map (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype)
          (⋀[R]^r M).subtype)) := by
  rw [tripleLeftι, Category.assoc, tripleLeftOuterι_realize]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t c
  have ht := congrArg (fun f => f.hom t) (tensorDegreeι_realize R M p q (p + q) rfl)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at ht
  change TensorProduct.assoc R E E E
      ((tensorDegreeRealize R M (p + q)).hom
        ((tensorDegreeι R M p q (p + q) rfl).hom t) ⊗ₜ[R] (c : E)) =
    TensorProduct.assoc R E E E
      (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype t ⊗ₜ[R] (c : E))
  rw [ht]

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. In degree n : ℕ, tripleAssociator is the graded tensor associator tripleLeftDegree n
→ tripleRightDegree n. On a homogeneous triple it is the ordinary map (a⊗b)⊗c ↦ a⊗(b⊗c), without
an interchange sign. -/
def tripleAssociator (n : ℕ) : tripleLeftDegree R M n ⟶ tripleRightDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact (GradedObject.Monoidal.associator 𝓔 𝓔 𝓔).hom n

@[reassoc]
theorem tripleLeftι_associator (p q r n : ℕ) (h : p + q + r = n) :
    tripleLeftι R M p q r n h ≫ tripleAssociator R M n =
      ModuleCat.ofHom ((TensorProduct.assoc R (⋀[R]^p M) (⋀[R]^q M) (⋀[R]^r M)).toLinearMap) ≫
        tripleRightι R M p q r n h := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ιTensorObj₃'_associator_hom 𝓔 𝓔 𝓔 p q r n h

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For every n : ℕ, tripleAssociator followed by tripleRightRealize equals
tripleLeftRealize. Both maps land in E⊗(E⊗E), with the ordinary tensor associator built into the
left realization. -/
theorem tripleAssociator_realize (n : ℕ) :
    tripleAssociator R M n ≫ tripleRightRealize R M n = tripleLeftRealize R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  change tripleLeftι R M p q r n h ≫ _ = tripleLeftι R M p q r n h ≫ _
  rw [← Category.assoc, tripleLeftι_associator, Category.assoc,
    tripleRightι_realize, tripleLeftι_realize]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t c
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        TensorProduct.assoc_tmul, TensorProduct.map_tmul, Submodule.subtype_apply]
      change TensorProduct.map (⋀[R]^p M).subtype
          (TensorProduct.map (⋀[R]^q M).subtype (⋀[R]^r M).subtype)
          (TensorProduct.assoc R (⋀[R]^p M) (⋀[R]^q M) (⋀[R]^r M)
            ((a ⊗ₜ[R] b) ⊗ₜ[R] c)) =
        TensorProduct.assoc R E E E (((a : E) ⊗ₜ[R] (b : E)) ⊗ₜ[R] (c : E))
      rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.assoc_tmul]
      rfl
  | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. In total degree n, gradedRightComul is id_{E•}⊗Δ, taking Tₙ to tripleRightDegree n
by applying the graded exterior coproduct to the right factor. -/
def gradedRightComul (n : ℕ) : tensorDegree R M n ⟶ tripleRightDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorHom (𝟙 𝓔) (gradedCoproduct R M) n

/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. In total degree n, gradedLeftComul is Δ⊗id_{E•}, taking Tₙ to tripleLeftDegree n by
applying the graded exterior coproduct to the left factor. -/
def gradedLeftComul (n : ℕ) : tensorDegree R M n ⟶ tripleLeftDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.tensorHom (gradedCoproduct R M) (𝟙 𝓔) n

@[reassoc]
theorem tensorDegreeι_rightComul (p q n : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ gradedRightComul R M n =
      ModuleCat.ofHom (TensorProduct.map LinearMap.id (gradedCoproduct R M q).hom) ≫
        tripleRightOuterι R M p q n h := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ι_tensorHom (𝟙 𝓔) (gradedCoproduct R M) p q n h

@[reassoc]
theorem tensorDegreeι_leftComul (p q n : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ gradedLeftComul R M n =
      ModuleCat.ofHom (TensorProduct.map (gradedCoproduct R M p).hom LinearMap.id) ≫
        tripleLeftOuterι R M p q n h := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v}
    (R := R)
  exact GradedObject.Monoidal.ι_tensorHom (gradedCoproduct R M) (𝟙 𝓔) p q n h

theorem gradedRightComul_realize (n : ℕ) :
    gradedRightComul R M n ≫ tripleRightRealize R M n =
      tensorDegreeRealize R M n ≫ ModuleCat.ofHom ((coproduct R M).lTensor E) := by
  apply tensorDegree_hom_ext R M n
  intro p q h
  rw [← Category.assoc, tensorDegreeι_rightComul, Category.assoc, tripleRightOuterι_realize,
    ← Category.assoc, tensorDegreeι_realize]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  have hb := congrArg (fun f => f.hom b) (gradedCoproduct_realize R M q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hb
  change (a : E) ⊗ₜ[R] (tensorDegreeRealize R M q).hom ((gradedCoproduct R M q).hom b) =
    (a : E) ⊗ₜ[R] coproduct R M (b : E)
  exact congrArg (fun z : P => (a : E) ⊗ₜ[R] z) hb

theorem gradedLeftComul_realize (n : ℕ) :
    gradedLeftComul R M n ≫ tripleLeftRealize R M n = tensorDegreeRealize R M n ≫
      ModuleCat.ofHom ((TensorProduct.assoc R E E E).toLinearMap.comp
        ((coproduct R M).rTensor E)) := by
  apply tensorDegree_hom_ext R M n
  intro p q h
  have hleft := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ tripleLeftRealize R M n) (tensorDegreeι_leftComul R M p q n h)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => ModuleCat.ofHom
          (TensorProduct.map (gradedCoproduct R M p).hom
            (LinearMap.id : (⋀[R]^q M) →ₗ[R] (⋀[R]^q M))) ≫ z)
          (tripleLeftOuterι_realize R M p q n h))))
  have hright := (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ ModuleCat.ofHom
      ((TensorProduct.assoc R E E E).toLinearMap.comp ((coproduct R M).rTensor E)))
        (tensorDegreeι_realize R M p q n h))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  let a₀ : ⋀[R]^p M := a
  have ha := congrArg (fun f => f.hom (show gradedExterior R M p from a₀))
    (gradedCoproduct_realize R M p)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at ha
  change TensorProduct.assoc R E E E
      ((tensorDegreeRealize R M p).hom ((gradedCoproduct R M p).hom a₀) ⊗ₜ[R] (b : E)) =
    TensorProduct.assoc R E E E (coproduct R M (a₀ : E) ⊗ₜ[R] (b : E))
  exact congrArg (fun z : P => TensorProduct.assoc R E E E (z ⊗ₜ[R] (b : E))) ha


/-- Let R be a commutative ring and M an R-module with additive inverses. Put
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q), in the module universe max(u,v) for
R,M in u,v. For every n : ℕ, Δₙ ≫ gradedRightComulₙ = Δₙ ≫ gradedLeftComulₙ ≫ tripleAssociatorₙ.
This is the equality of the two iterated exterior coproducts after reassociation. -/
theorem gradedCoproduct_coassoc (n : ℕ) :
    gradedCoproduct R M n ≫ gradedRightComul R M n =
      gradedCoproduct R M n ≫ gradedLeftComul R M n ≫ tripleAssociator R M n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a₀ : ⋀[R]^n M := a
  apply tripleRightRealize_injective R M n
  let t : tensorDegree R M n := (gradedCoproduct R M n).hom a
  let u : tripleLeftDegree R M n := (gradedLeftComul R M n).hom t
  let v : tripleRightDegree R M n := (gradedRightComul R M n).hom t
  have hc := congrArg (fun f => f.hom a) (gradedCoproduct_realize R M n)
  change (tensorDegreeRealize R M n).hom t = coproduct R M (a₀ : E) at hc
  have hr := congrArg (fun f => f.hom t) (gradedRightComul_realize R M n)
  change (tripleRightRealize R M n).hom v =
    (coproduct R M).lTensor E ((tensorDegreeRealize R M n).hom t) at hr
  have hl := congrArg (fun f => f.hom t) (gradedLeftComul_realize R M n)
  change (tripleLeftRealize R M n).hom u =
    TensorProduct.assoc R E E E ((coproduct R M).rTensor E
      ((tensorDegreeRealize R M n).hom t)) at hl
  have ha := congrArg (fun f => f.hom u) (tripleAssociator_realize R M n)
  change (tripleRightRealize R M n).hom ((tripleAssociator R M n).hom u) =
    (tripleLeftRealize R M n).hom u at ha
  change (tripleRightRealize R M n).hom v =
    (tripleRightRealize R M n).hom ((tripleAssociator R M n).hom u)
  exact (hr.trans (congrArg ((coproduct R M).lTensor E) hc)).trans
    ((coproduct_coassoc_apply R M (a₀ : E)).symm.trans
      ((hl.trans (congrArg (fun z => TensorProduct.assoc R E E E
        ((coproduct R M).rTensor E z)) hc)).symm.trans ha.symm))

end ExteriorAlgebra
