/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGrading
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.GradedObject.Monoidal

/-!
# Tensor degrees of the exterior grading

For a commutative ring R and an R-module M, write E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and
Tₙ=⊕_{p+q=n}Eₚ⊗_RE_q. The homogeneous component inclusions induce a realization rₙ:Tₙ → E⊗_RE.
The finite sum of bidegree projections defines Lₙ:E⊗E → Tₙ.

The identity Lₙrₙ=id_{Tₙ} makes rₙ a split injection. The other composite rₙLₙ is total-degree-n
reconstruction and fixes every tensor in that homogeneous total-degree submodule. These
splittings require no flatness or freeness assumption.

The exterior coproduct preserves total degree, so its restriction to Eₙ followed by Lₙ gives the
graded coproduct Eₙ → Tₙ. Realizing it returns the exterior coproduct in E⊗E. The category of
R-modules is placed in max(u,v), with R and M in their separate universes u,v.
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
local notation "π" => exteriorPower.projection R M

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedExterior is the ℕ-graded
R-module n ↦ Eₙ. It is placed in the module universe max(u,v) when R,M lie in universes u,v. -/
def gradedExterior : GradedObject ℕ (ModuleCat.{max u v} R) := fun n => ModuleCat.of R (⋀[R]^n M)

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For n : ℕ, tensorDegree R M n is the
convolution graded-tensor term Tₙ=⊕_{p+q=n}(Eₚ⊗_RE_q), in the common R-module category max(u,v). -/
def tensorDegree (n : ℕ) : (ModuleCat.{max u v} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObj (gradedExterior R M) (gradedExterior R M) n

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For p,q,n : ℕ with p+q=n,
tensorDegreeι is the coproduct inclusion Eₚ⊗_RE_q → Tₙ of that homogeneous bidegree summand. -/
def tensorDegreeι (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ tensorDegree R M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.ιTensorObj (gradedExterior R M) (gradedExterior R M) p q n h

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For an R-module A in the common
universe and maps fₚq:Eₚ⊗_RE_q → A for every p+q=n, tensorDegreeDesc is the unique map Tₙ → A
restricting to fₚq on each homogeneous summand. -/
def tensorDegreeDesc (n : ℕ) {A : (ModuleCat.{max u v} R)}
    (f : ∀ p q (h : p + q = n), ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ A) :
    tensorDegree R M n ⟶ A := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObjDesc f

@[reassoc]
theorem tensorDegreeι_desc (n : ℕ) {A : (ModuleCat.{max u v} R)}
    (f : ∀ p q (h : p + q = n), ModuleCat.of R ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) ⟶ A)
    (p q : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ tensorDegreeDesc R M n f = f p q h := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.ι_tensorObjDesc
    (X₁ := gradedExterior R M) (X₂ := gradedExterior R M) f p q h

theorem tensorDegree_hom_ext (n : ℕ) {A : (ModuleCat.{max u v} R)}
    {f g : tensorDegree R M n ⟶ A}
    (hfg : ∀ p q (h : p + q = n), tensorDegreeι R M p q n h ≫ f =
      tensorDegreeι R M p q n h ≫ g) : f = g := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact GradedObject.Monoidal.tensorObj_ext f g hfg

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). tensorDegreeRealize rₙ:Tₙ → E⊗_RE is
induced by the exterior component inclusions: rₙ sends the (p,q)-summand tensor a⊗b to the same
tensor of a,b in E, for p+q=n. -/
def tensorDegreeRealize (n : ℕ) : tensorDegree R M n ⟶ ModuleCat.of R P :=
  tensorDegreeDesc R M n (fun p q _ =>
    ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype))

@[reassoc]
theorem tensorDegreeι_realize (p q n : ℕ) (h : p + q = n) :
    tensorDegreeι R M p q n h ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom (TensorProduct.map (⋀[R]^p M).subtype (⋀[R]^q M).subtype) :=
  tensorDegreeι_desc R M n _ p q h

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). Let πₚ:E → Eₚ be the exterior
projections. tensorDegreeLift Lₙ:E⊗E → Tₙ is ∑_{p=0}ⁿ ι_{p,n-p} ∘ (πₚ⊗π_{n-p}), the finite
projection onto all bidegrees of total degree n. -/
def tensorDegreeLift (n : ℕ) : ModuleCat.of R P ⟶ tensorDegree R M n :=
  ∑ p : Fin (n + 1), ModuleCat.ofHom (TensorProduct.map (π p.val) (π (n - p.val))) ≫
    tensorDegreeι R M p.val (n - p.val) n (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For n : ℕ, Lₙ followed by rₙ equals
degreeTensorReconstruction R M n on E⊗E. It is the sum of the homogeneous bidegree projections
πₚ⊗π_{n-p}, with their inclusions back into E⊗E. -/
theorem tensorDegreeLift_realize (n : ℕ) :
    tensorDegreeLift R M n ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom (degreeTensorReconstruction R M n) := by
  apply ModuleCat.hom_ext
  simp only [tensorDegreeLift, Preadditive.sum_comp, Category.assoc,
    tensorDegreeι_realize, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rfl

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For every n : ℕ, tensorDegreeRealize
rₙ followed by tensorDegreeLift Lₙ is the identity on Tₙ. -/
theorem tensorDegreeRealize_lift (n : ℕ) :
    tensorDegreeRealize R M n ≫ tensorDegreeLift R M n = 𝟙 (tensorDegree R M n) := by
  apply tensorDegree_hom_ext R M n
  intro i j hij
  rw [tensorDegreeι_realize_assoc]
  unfold tensorDegreeLift
  rw [Preadditive.comp_sum]
  have hi : i < n + 1 := Nat.lt_succ_of_le (Nat.le.intro hij)
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hni : n - p.val = j := by change n - i = j; rw [← hij, Nat.add_sub_cancel_left]
  rw [Finset.sum_eq_single p]
  · have hmaps : (TensorProduct.map (π i) (π j)).comp
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^j M).subtype) = LinearMap.id := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_subtype_apply, LinearMap.id_apply]
    subst j
    have hc : ModuleCat.ofHom
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^(n - p.val) M).subtype) ≫
        ModuleCat.ofHom (TensorProduct.map (π i) (π (n - p.val))) =
        𝟙 (ModuleCat.of R ((⋀[R]^i M) ⊗[R] (⋀[R]^(n - p.val) M))) := by
      apply ModuleCat.hom_ext
      exact hmaps
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ tensorDegreeι R M i (n - p.val) n hij) hc).trans
        (Category.id_comp _))
  · intro q hq hqp
    have hiq : i ≠ q.val := fun hiq => hqp (Fin.ext hiq.symm)
    have hmaps : (TensorProduct.map (π q.val) (π (n - q.val))).comp
        (TensorProduct.map (⋀[R]^i M).subtype (⋀[R]^j M).subtype) = 0 := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
        exteriorPower.projection_eq_zero_of_mem R M q.val i hiq a a.property,
        TensorProduct.zero_tmul, LinearMap.zero_apply]
    rw [← Category.assoc, ← ModuleCat.ofHom_comp, hmaps, ModuleCat.ofHom_zero,
      zero_comp]
  · intro hp
    exact False.elim (hp (Finset.mem_univ p))

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For every n : ℕ, the underlying map of
tensorDegreeRealize rₙ:Tₙ → E⊗E is injective, with left inverse Lₙ. No flatness assumption is
needed because the homogeneous projections split the inclusions. -/
theorem tensorDegreeRealize_injective (n : ℕ) :
    Function.Injective (tensorDegreeRealize R M n).hom := by
  apply Function.LeftInverse.injective
  intro x
  exact congrArg (fun f => f.hom x) (tensorDegreeRealize_lift R M n)

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). If t ∈ E⊗E belongs to coproductDegree
R M n, the total-degree-n submodule, then realizing its lifted degree coordinate recovers t:
rₙ(Lₙ(t))=t. -/
theorem tensorDegreeRealize_lift_of_mem (n : ℕ) (t : P) (ht : t ∈ coproductDegree R M n) :
    (tensorDegreeRealize R M n).hom ((tensorDegreeLift R M n).hom t) = t := by
  have h := congrArg (fun f => f.hom t) (tensorDegreeLift_realize R M n)
  exact h.trans (degreeTensorReconstruction_of_mem R M n t ht)

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). gradedTensorSquare is the ℕ-graded
R-module n ↦ Tₙ, the tensor product of the two exterior gradings in the common module category. -/
def gradedTensorSquare : GradedObject ℕ (ModuleCat.{max u v} R) := tensorDegree R M

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). In each degree n, restrict the
exterior coproduct Δ:E → E⊗E to Eₙ and follow it by Lₙ. These maps define gradedCoproduct:E• →
gradedTensorSquare, with degree-preserving target Tₙ. -/
def gradedCoproduct : gradedExterior R M ⟶ gradedTensorSquare R M := fun n =>
  ModuleCat.ofHom ((coproduct R M).comp (⋀[R]^n M).subtype) ≫ tensorDegreeLift R M n

/-- Let R be a commutative ring and M an R-module with additive inverses. Write
E=ExteriorAlgebra(R,M), Eₙ=∧ⁿ_RM and Tₙ=⊕ₚ₊q₌ₙ(Eₚ⊗_RE_q). For every n : ℕ, gradedCoproduct R M n
followed by rₙ equals the exterior coproduct restricted along Eₙ ↪ E. Thus rₙ(Δₙ(a))=Δ(a) for a
∈ Eₙ. -/
theorem gradedCoproduct_realize (n : ℕ) :
    gradedCoproduct R M n ≫ tensorDegreeRealize R M n =
      ModuleCat.ofHom ((coproduct R M).comp (⋀[R]^n M).subtype) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a₀ : ⋀[R]^n M := a
  exact tensorDegreeRealize_lift_of_mem R M n _
    (coproduct_mem_degree R M n (a₀ : E) a₀.property)

end ExteriorAlgebra
