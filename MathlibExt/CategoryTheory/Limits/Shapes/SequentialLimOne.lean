/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Sequential inverse limits and concrete `lim¹`

For a tower `A : ℕᵒᵖ ⥤ C`, the standard difference on the product of its
objects has `n`th coordinate `aₙ - tₙ aₙ₊₁`. Its kernel is the inverse limit,
and its cokernel is the concrete sequential `lim¹` object. No identification
with a right-derived functor is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- The countable product of the objects in a tower. -/
abbrev sequentialProduct (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] : C :=
  ∏ᶜ fun n : ℕ => A.obj (op n)

/-- The componentwise map of sequential products induced by a map of towers. -/
noncomputable def sequentialProductMap
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C] (α : A ⟶ B) :
    sequentialProduct A ⟶ sequentialProduct B :=
  Pi.map fun n => α.app (op n)

/-- The component formula for the map of sequential products. -/
@[reassoc (attr := simp)]
theorem sequentialProductMap_π
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C]
    (α : A ⟶ B) (n : ℕ) :
    sequentialProductMap α ≫ Pi.π (fun n : ℕ => B.obj (op n)) n =
      Pi.π (fun n : ℕ => A.obj (op n)) n ≫ α.app (op n) := by
  exact Pi.map_π (fun n => α.app (op n)) n

/-- The map of sequential products preserves identities. -/
@[simp]
theorem sequentialProductMap_id
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] :
    sequentialProductMap (𝟙 A) = 𝟙 (sequentialProduct A) := by
  change Pi.map (fun n : ℕ => 𝟙 (A.obj (op n))) = 𝟙 _
  exact Pi.map_id

/-- The map of sequential products preserves composition. -/
@[reassoc]
theorem sequentialProductMap_comp
    {A B D : ℕᵒᵖ ⥤ C} [HasCountableProducts C]
    (α : A ⟶ B) (β : B ⟶ D) :
    sequentialProductMap α ≫ sequentialProductMap β =
      sequentialProductMap (α ≫ β) := by
  change Pi.map (fun n : ℕ => α.app (op n)) ≫
      Pi.map (fun n : ℕ => β.app (op n)) =
    Pi.map (fun n : ℕ => α.app (op n) ≫ β.app (op n))
  exact Pi.map_comp_map _ _

/-- The canonical map from a chosen inverse limit to the product of the
objects in the tower. -/
noncomputable def sequentialLimitToProduct
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] [HasLimit A] :
    limit A ⟶ sequentialProduct A :=
  Pi.lift fun n => limit.π A (op n)

/-- The coordinates of the canonical map from an inverse limit to the
sequential product. -/
@[reassoc (attr := simp)]
theorem sequentialLimitToProduct_π
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] [HasLimit A] (n : ℕ) :
    sequentialLimitToProduct A ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      limit.π A (op n) := by
  simp [sequentialLimitToProduct]

/-- The canonical map from a chosen inverse limit to the sequential product
is natural in the tower. -/
@[reassoc]
theorem sequentialLimitToProduct_naturality
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C]
    [HasLimit A] [HasLimit B] (α : A ⟶ B) :
    sequentialLimitToProduct A ≫ sequentialProductMap α =
      limMap α ≫ sequentialLimitToProduct B := by
  apply Pi.hom_ext
  intro n
  simp

/-- The canonical map from a chosen sequential limit to the product is a
monomorphism. -/
noncomputable instance sequentialLimitToProduct_mono
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] [HasLimit A] :
    Mono (sequentialLimitToProduct A) := by
  constructor
  intro Z f g h
  apply limit.hom_ext
  rintro ⟨n⟩
  have h' := congrArg
    (fun k => k ≫ Pi.π (fun n : ℕ => A.obj (op n)) n) h
  simpa only [Category.assoc, sequentialLimitToProduct_π] using h'

section Preadditive

variable [Preadditive C] [HasCountableProducts C]

/-- The standard `1 - shift` difference on the product of a tower. -/
noncomputable def sequentialDifference (A : ℕᵒᵖ ⥤ C) :
    sequentialProduct A ⟶ sequentialProduct A :=
  Pi.lift fun n =>
    Pi.π (fun n : ℕ => A.obj (op n)) n -
      Pi.π (fun n : ℕ => A.obj (op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op

/-- The projection formula fixing the sign of the standard sequential
difference. -/
@[reassoc (attr := simp)]
theorem sequentialDifference_π (A : ℕᵒᵖ ⥤ C) (n : ℕ) :
    sequentialDifference A ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      Pi.π (fun n : ℕ => A.obj (op n)) n -
        Pi.π (fun n : ℕ => A.obj (op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op := by
  simp [sequentialDifference]

/-- The standard sequential difference is natural in maps of towers. -/
@[reassoc]
theorem sequentialDifference_naturality
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialProductMap α ≫ sequentialDifference B =
      sequentialDifference A ≫ sequentialProductMap α := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, sequentialDifference_π,
    sequentialDifference_π_assoc, sequentialProductMap_π,
    sequentialProductMap_π_assoc, Preadditive.comp_sub,
    Preadditive.sub_comp]
  rw [α.naturality]

section Kernels

variable [HasKernels C]

/-- The cone on a tower whose point is the kernel of its standard sequential
difference. -/
noncomputable abbrev sequentialKernelCone (A : ℕᵒᵖ ⥤ C) : Cone A where
  pt := kernel (sequentialDifference A)
  π := NatTrans.ofOpSequence
    (fun n => kernel.ι (sequentialDifference A) ≫
      Pi.π (fun n : ℕ => A.obj (op n)) n)
    (fun n => by
      have h := congrArg
        (fun f => f ≫ Pi.π (fun n : ℕ => A.obj (op n)) n)
        (kernel.condition (sequentialDifference A))
      simp only [Category.assoc, sequentialDifference_π,
        Preadditive.comp_sub, zero_comp] at h
      simpa using sub_eq_zero.mp h)

/-- The point of the sequential kernel cone is the kernel of the difference. -/
@[simp]
theorem sequentialKernelCone_pt (A : ℕᵒᵖ ⥤ C) :
    (sequentialKernelCone A).pt = kernel (sequentialDifference A) :=
  rfl

/-- The legs of the sequential kernel cone are the kernel inclusion followed
by the product projections. -/
@[simp]
theorem sequentialKernelCone_π_app (A : ℕᵒᵖ ⥤ C) (n : ℕ) :
    (sequentialKernelCone A).π.app (op n) =
      kernel.ι (sequentialDifference A) ≫
        Pi.π (fun n : ℕ => A.obj (op n)) n :=
  by
    unfold sequentialKernelCone
    rfl

/-- The kernel cone of the standard sequential difference is limiting. -/
noncomputable def sequentialKernelConeIsLimit (A : ℕᵒᵖ ⥤ C) :
    IsLimit (sequentialKernelCone A) := by
  unfold sequentialKernelCone
  let q (s : Cone A) : s.pt ⟶ sequentialProduct A :=
    Pi.lift fun n => s.π.app (op n)
  have q_π (s : Cone A) (n : ℕ) :
      q s ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
        s.π.app (op n) := by
    simp [q]
  have q_difference (s : Cone A) : q s ≫ sequentialDifference A = 0 := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, sequentialDifference_π, Preadditive.comp_sub,
      zero_comp, q_π]
    rw [← Category.assoc, q_π, s.w (homOfLE (Nat.le_succ n)).op]
    simp
  refine
    { lift := fun s => kernel.lift (sequentialDifference A) (q s)
        (q_difference s)
      fac := ?_
      uniq := ?_ }
  · intro s j
    rcases j with ⟨n⟩
    change kernel.lift (sequentialDifference A) (q s) (q_difference s) ≫
        (kernel.ι (sequentialDifference A) ≫
          Pi.π (fun n : ℕ => A.obj (op n)) n) = s.π.app (op n)
    rw [← Category.assoc, kernel.lift_ι, q_π]
  · intro s m hm
    apply (cancel_mono (kernel.ι (sequentialDifference A))).1
    apply Pi.hom_ext
    intro n
    calc
      (m ≫ kernel.ι (sequentialDifference A)) ≫
          Pi.π (fun n : ℕ => A.obj (op n)) n =
        m ≫ (kernel.ι (sequentialDifference A) ≫
          Pi.π (fun n : ℕ => A.obj (op n)) n) :=
          Category.assoc _ _ _
      _ = s.π.app (op n) := hm (op n)
      _ = q s ≫ Pi.π (fun n : ℕ => A.obj (op n)) n :=
        (q_π s n).symm
      _ = (kernel.lift (sequentialDifference A) (q s) (q_difference s) ≫
          kernel.ι (sequentialDifference A)) ≫
            Pi.π (fun n : ℕ => A.obj (op n)) n := by
        rw [kernel.lift_ι]

/-- Explicit evidence that every tower has a limit when countable products
and kernels exist. This is deliberately not a global instance. -/
theorem hasLimit_of_sequential_product_and_kernel
    (A : ℕᵒᵖ ⥤ C) : HasLimit A :=
  HasLimit.mk ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩

/-- A chosen inverse limit of a tower is canonically isomorphic to the kernel
of its standard difference. -/
noncomputable def sequentialLimitKernelIso (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    limit A ≅ kernel (sequentialDifference A) :=
  limit.isoLimitCone
    ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩

/-- The forward kernel comparison followed by the kernel inclusion is the
canonical map from the chosen limit to the sequential product. -/
@[reassoc (attr := simp)]
theorem sequentialLimitKernelIso_hom_ι
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitKernelIso A).hom ≫
        kernel.ι (sequentialDifference A) =
      sequentialLimitToProduct A := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, sequentialLimitToProduct_π]
  have h := limit.isoLimitCone_hom_π
    ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩ (op n)
  rw [sequentialKernelCone_π_app] at h
  simpa only [sequentialLimitKernelIso, Category.assoc] using h

/-- The inverse kernel comparison followed by the chosen limit-to-product map
is the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem sequentialLimitKernelIso_inv_comp_toProduct
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitKernelIso A).inv ≫ sequentialLimitToProduct A =
      kernel.ι (sequentialDifference A) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, sequentialLimitToProduct_π]
  have h := limit.isoLimitCone_inv_π
    ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩ (op n)
  rw [sequentialKernelCone_π_app] at h
  simpa only [sequentialLimitKernelIso] using h

end Kernels

/-- The canonical map from a chosen limit lands in the kernel of the standard
sequential difference. -/
@[reassoc (attr := simp)]
theorem sequentialLimitToProduct_comp_difference
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    sequentialLimitToProduct A ≫ sequentialDifference A = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, sequentialDifference_π,
    sequentialLimitToProduct_π, sequentialLimitToProduct_π_assoc,
    Preadditive.comp_sub, zero_comp]
  rw [limit.w A (homOfLE (Nat.le_succ n)).op]
  simp

/-- The canonical three-term complex
`limit A ⟶ sequentialProduct A ⟶ sequentialProduct A`. -/
noncomputable def sequentialLimitShortComplex
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] : ShortComplex C :=
  ShortComplex.mk (sequentialLimitToProduct A) (sequentialDifference A)
    (sequentialLimitToProduct_comp_difference A)

/-- The first map of the canonical sequential-limit short complex. -/
@[simp]
theorem sequentialLimitShortComplex_f
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitShortComplex A).f = sequentialLimitToProduct A :=
  rfl

/-- The second map of the canonical sequential-limit short complex. -/
@[simp]
theorem sequentialLimitShortComplex_g
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitShortComplex A).g = sequentialDifference A :=
  rfl

/-- The first map of the canonical sequential-limit short complex is mono. -/
noncomputable instance sequentialLimitShortComplex_mono_f
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    Mono (sequentialLimitShortComplex A).f := by
  change Mono (sequentialLimitToProduct A)
  infer_instance

section Cokernels

variable [HasCokernels C]

/-- The concrete sequential `lim¹`, defined as the cokernel of the standard
difference. -/
noncomputable def sequentialLimOne (A : ℕᵒᵖ ⥤ C) : C :=
  cokernel (sequentialDifference A)

/-- The quotient from the sequential product to concrete sequential `lim¹`. -/
noncomputable def sequentialLimOneπ (A : ℕᵒᵖ ⥤ C) :
    sequentialProduct A ⟶ sequentialLimOne A :=
  cokernel.π (sequentialDifference A)

/-- The difference followed by the concrete `lim¹` quotient is zero. -/
@[reassoc (attr := simp)]
theorem sequentialDifference_comp_limOneπ (A : ℕᵒᵖ ⥤ C) :
    sequentialDifference A ≫ sequentialLimOneπ A = 0 :=
  cokernel.condition _

/-- The map on concrete sequential `lim¹` induced by a map of towers. -/
noncomputable def sequentialLimOneMap
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOne A ⟶ sequentialLimOne B :=
  cokernel.map (sequentialDifference A) (sequentialDifference B)
    (sequentialProductMap α) (sequentialProductMap α)
    (sequentialDifference_naturality α).symm

/-- The concrete `lim¹` map is characterized by the quotient projections. -/
@[reassoc (attr := simp)]
theorem sequentialLimOneπ_comp_map
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOneπ A ≫ sequentialLimOneMap α =
      sequentialProductMap α ≫ sequentialLimOneπ B := by
  dsimp only [sequentialLimOneπ, sequentialLimOneMap, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- The quotient to concrete sequential `lim¹` is an epimorphism. -/
noncomputable instance sequentialLimOneπ_epi (A : ℕᵒᵖ ⥤ C) :
    Epi (sequentialLimOneπ A) := by
  change Epi (cokernel.π (sequentialDifference A))
  infer_instance

/-- Concrete sequential `lim¹` vanishes when the standard difference is epi. -/
theorem isZero_sequentialLimOne_of_epi
    (A : ℕᵒᵖ ⥤ C) [Epi (sequentialDifference A)] :
    IsZero (sequentialLimOne A) :=
  isZero_cokernel_of_epi (sequentialDifference A)

/-- The induced map on concrete sequential `lim¹` preserves identities. -/
@[simp]
theorem sequentialLimOneMap_id (A : ℕᵒᵖ ⥤ C) :
    sequentialLimOneMap (𝟙 A) = 𝟙 (sequentialLimOne A) := by
  apply (cancel_epi (sequentialLimOneπ A)).1
  simp

/-- The induced map on concrete sequential `lim¹` preserves composition. -/
@[reassoc]
theorem sequentialLimOneMap_comp
    {A B D : ℕᵒᵖ ⥤ C} (α : A ⟶ B) (β : B ⟶ D) :
    sequentialLimOneMap (α ≫ β) =
      sequentialLimOneMap α ≫ sequentialLimOneMap β := by
  apply (cancel_epi (sequentialLimOneπ A)).1
  calc
    sequentialLimOneπ A ≫ sequentialLimOneMap (α ≫ β) =
        sequentialProductMap (α ≫ β) ≫ sequentialLimOneπ D := by simp
    _ = (sequentialProductMap α ≫ sequentialProductMap β) ≫
        sequentialLimOneπ D := by rw [sequentialProductMap_comp]
    _ = sequentialProductMap α ≫
        (sequentialProductMap β ≫ sequentialLimOneπ D) := by simp
    _ = sequentialProductMap α ≫
        (sequentialLimOneπ B ≫ sequentialLimOneMap β) := by simp
    _ = (sequentialProductMap α ≫ sequentialLimOneπ B) ≫
        sequentialLimOneMap β := by simp
    _ = (sequentialLimOneπ A ≫ sequentialLimOneMap α) ≫
        sequentialLimOneMap β := by simp
    _ = sequentialLimOneπ A ≫
        (sequentialLimOneMap α ≫ sequentialLimOneMap β) := by simp

/-- Concrete sequential `lim¹` as a covariant functor of towers. -/
noncomputable def sequentialLimOneFunctor : (ℕᵒᵖ ⥤ C) ⥤ C where
  obj := sequentialLimOne
  map := sequentialLimOneMap
  map_id := sequentialLimOneMap_id
  map_comp := sequentialLimOneMap_comp

/-- The object field of the concrete sequential `lim¹` functor. -/
@[simp]
theorem sequentialLimOneFunctor_obj (A : ℕᵒᵖ ⥤ C) :
    sequentialLimOneFunctor.obj A = sequentialLimOne A :=
  rfl

/-- The map field of the concrete sequential `lim¹` functor. -/
@[simp]
theorem sequentialLimOneFunctor_map
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOneFunctor.map α = sequentialLimOneMap α :=
  rfl

end Cokernels

end Preadditive

section Abelian

variable [Abelian C] [HasCountableProducts C]

/-- Exactness at the second product in the canonical sequential-limit
sequence. -/
theorem sequentialDifference_limOne_exact (A : ℕᵒᵖ ⥤ C) :
    (ShortComplex.mk (sequentialDifference A) (sequentialLimOneπ A)
      (sequentialDifference_comp_limOneπ A)).Exact := by
  simpa only [sequentialLimOne, sequentialLimOneπ] using
    ShortComplex.exact_cokernel (sequentialDifference A)

/-- Exactness at the first product in the canonical sequential-limit
sequence. -/
theorem sequentialLimitShortComplex_exact
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitShortComplex A).Exact := by
  let S := ShortComplex.mk (kernel.ι (sequentialDifference A))
    (sequentialDifference A) (kernel.condition _)
  let e : S ≅ sequentialLimitShortComplex A := ShortComplex.isoMk
    (sequentialLimitKernelIso A).symm (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [S]
      change (sequentialLimitKernelIso A).inv ≫
          sequentialLimitToProduct A =
        kernel.ι (sequentialDifference A) ≫ 𝟙 _
      exact (sequentialLimitKernelIso_inv_comp_toProduct A).trans
        (Category.comp_id _).symm)
    (by
      dsimp only [S]
      change 𝟙 (sequentialProduct A) ≫ sequentialDifference A =
        sequentialDifference A ≫ 𝟙 (sequentialProduct A)
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact ShortComplex.exact_of_iso e (ShortComplex.exact_kernel _)

end Abelian

end CategoryTheory.Limits

end
