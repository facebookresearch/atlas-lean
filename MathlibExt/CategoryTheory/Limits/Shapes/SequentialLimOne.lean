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
# Inverse limits and sequential difference cokernels

Let A : ℕᵒᵖ ⥤ C be an inverse tower with objects A_n and transitions t_n : A_{n+1} → A_n. Its
countable product P_A = ∏ₙA_n is functorial in tower maps. In a preadditive category, the
difference d_A : P_A → P_A has coordinate a_n − t_n(a_{n+1}).

When kernels exist, Ker(d_A) with its product projections is a limit of A. A chosen limit maps
monomorphically into P_A and is canonically isomorphic to this kernel. When cokernels exist,
the concrete sequential lim¹ object is Coker(d_A), functorially in tower maps.

In an abelian category with countable products, these constructions give an exact sequence 0 →
limit A → P_A → P_A → lim¹ A → 0. The middle map is d_A with the displayed subtraction sign.
The object and morphism universes of C are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Product object of an inverse tower.

For an inverse tower A : ℕᵒᵖ ⥤ C in a category with countable products, sequentialProduct A is
P_A = ∏ₙ A_n, where A_n = A.obj(op n). -/
abbrev sequentialProduct (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] : C :=
  ∏ᶜ fun n : ℕ => A.obj (op n)

/-- Componentwise product map of inverse towers.

For a tower map α : A → B in a category with countable products, P(α) : P_A → P_B has n-th
coordinate π_A,n ≫ α_n. It is the product map of the levelwise components α_n. -/
noncomputable def sequentialProductMap
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C] (α : A ⟶ B) :
    sequentialProduct A ⟶ sequentialProduct B :=
  Pi.map fun n => α.app (op n)

/-- Projection equation for a product map of towers.

For α : A → B and n : ℕ, the componentwise product map satisfies P(α) ≫ π_B,n = π_A,n ≫ α_n,
where P_A and P_B are the countable products of the tower objects. -/
@[reassoc (attr := simp)]
theorem sequentialProductMap_π
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C]
    (α : A ⟶ B) (n : ℕ) :
    sequentialProductMap α ≫ Pi.π (fun n : ℕ => B.obj (op n)) n =
      Pi.π (fun n : ℕ => A.obj (op n)) n ≫ α.app (op n) := by
  exact Pi.map_π (fun n => α.app (op n)) n

/-- Identity law for tower product maps.

For an inverse tower A in a category with countable products, the product map of the identity
tower morphism is the identity of P_A. -/
@[simp]
theorem sequentialProductMap_id
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] :
    sequentialProductMap (𝟙 A) = 𝟙 (sequentialProduct A) := by
  change Pi.map (fun n : ℕ => 𝟙 (A.obj (op n))) = 𝟙 _
  exact Pi.map_id

/-- Composition law for tower product maps.

For tower maps α : A → B and β : B → D in a category with countable products, P(α) ≫ P(β) =
P(α ≫ β). The equality holds on every coordinate by componentwise composition. -/
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

/-- Map from an inverse limit to its tower product.

For a tower A with a chosen limit and countable product P_A, define L_A : limit A → P_A by its
coordinates L_A ≫ π_A,n = limit.π A (op n). -/
noncomputable def sequentialLimitToProduct
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] [HasLimit A] :
    limit A ⟶ sequentialProduct A :=
  Pi.lift fun n => limit.π A (op n)

/-- Coordinates of the inverse-limit map to a product.

For a tower A with chosen limit and countable product, the n-th projection of L_A : limit A →
P_A is the limit leg: L_A ≫ π_A,n = limit.π A (op n). -/
@[reassoc (attr := simp)]
theorem sequentialLimitToProduct_π
    (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] [HasLimit A] (n : ℕ) :
    sequentialLimitToProduct A ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      limit.π A (op n) := by
  simp [sequentialLimitToProduct]

/-- Naturality of inverse-limit inclusion into tower products.

For a tower map α : A → B, with limits and countable products of both towers defined, L_A ≫
P(α) = limMap(α) ≫ L_B. Thus the product of the level maps commutes with the induced map of
inverse limits. -/
@[reassoc]
theorem sequentialLimitToProduct_naturality
    {A B : ℕᵒᵖ ⥤ C} [HasCountableProducts C]
    [HasLimit A] [HasLimit B] (α : A ⟶ B) :
    sequentialLimitToProduct A ≫ sequentialProductMap α =
      limMap α ≫ sequentialLimitToProduct B := by
  apply Pi.hom_ext
  intro n
  simp

/-- Monomorphism from an inverse limit to its tower product.

For a tower A with chosen limit and countable product, the canonical coordinate map L_A :
limit A → P_A is monic. Equality after L_A implies equality after every limit projection and
hence equality of maps into the limit. -/
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

/-- Identity-minus-shift map of an inverse tower.

Let C be preadditive with countable products and A an inverse tower with transitions t_n :
A_{n+1} → A_n. The standard difference d_A : P_A → P_A has n-th coordinate π_n − π_{n+1} ≫
t_n, corresponding to a_n − t_n(a_{n+1}). -/
noncomputable def sequentialDifference (A : ℕᵒᵖ ⥤ C) :
    sequentialProduct A ⟶ sequentialProduct A :=
  Pi.lift fun n =>
    Pi.π (fun n : ℕ => A.obj (op n)) n -
      Pi.π (fun n : ℕ => A.obj (op n)) (n + 1) ≫
        A.map (homOfLE (Nat.le_succ n)).op

/-- Signed coordinate formula for a sequential difference.

For an inverse tower A in a preadditive category with countable products, d_A ≫ π_n = π_n −
π_{n+1} ≫ t_n, where t_n : A_{n+1} → A_n is the successor transition. This fixes the
identity-minus-shift sign convention. -/
@[reassoc (attr := simp)]
theorem sequentialDifference_π (A : ℕᵒᵖ ⥤ C) (n : ℕ) :
    sequentialDifference A ≫ Pi.π (fun n : ℕ => A.obj (op n)) n =
      Pi.π (fun n : ℕ => A.obj (op n)) n -
        Pi.π (fun n : ℕ => A.obj (op n)) (n + 1) ≫
          A.map (homOfLE (Nat.le_succ n)).op := by
  simp [sequentialDifference]

/-- Naturality of the identity-minus-shift difference.

For a map α : A → B of inverse towers in a preadditive category with countable products, the
product maps intertwine the differences: P(α) ≫ d_B = d_A ≫ P(α). Naturality of α on the
successor transitions gives the coordinate equations. -/
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

/-- Cone on a tower from the kernel of its difference.

Let C be preadditive with countable products and kernels. For an inverse tower A, the object
Ker(d_A) carries a cone with n-th leg kernel.ι(d_A) ≫ π_A,n. The kernel equation d_A = 0 on
this object supplies compatibility with every successor transition. -/
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

/-- Vertex of the sequential difference kernel cone.

For a tower A in a preadditive category with countable products and kernels, the point of
sequentialKernelCone A is Ker(d_A), the kernel of its identity-minus-shift difference. -/
@[simp]
theorem sequentialKernelCone_pt (A : ℕᵒᵖ ⥤ C) :
    (sequentialKernelCone A).pt = kernel (sequentialDifference A) :=
  rfl

/-- Legs of the sequential difference kernel cone.

For a tower A in a preadditive category with countable products and kernels, the cone leg at
level n is kernel.ι(d_A) ≫ π_A,n : Ker(d_A) → A_n. -/
@[simp]
theorem sequentialKernelCone_π_app (A : ℕᵒᵖ ⥤ C) (n : ℕ) :
    (sequentialKernelCone A).π.app (op n) =
      kernel.ι (sequentialDifference A) ≫
        Pi.π (fun n : ℕ => A.obj (op n)) n :=
  by
    unfold sequentialKernelCone
    rfl

/-- Universal property of the sequential difference kernel cone.

In a preadditive category with countable products and kernels, Ker(d_A) with legs
kernel.ι(d_A) ≫ π_A,n is a limit of the tower A. A compatible cone first maps to P_A by its
legs, and the compatibility equations make this map factor uniquely through Ker(d_A). -/
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

/-- Existence of tower limits from products and kernels.

Every inverse tower A in a preadditive category with countable products and kernels has a
limit, represented by Ker(d_A) with its projection legs. -/
theorem hasLimit_of_sequential_product_and_kernel
    (A : ℕᵒᵖ ⥤ C) : HasLimit A :=
  HasLimit.mk ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩

/-- Isomorphism of an inverse limit with its difference kernel.

For an inverse tower A in a preadditive category with countable products and kernels, any
chosen limit is canonically isomorphic to Ker(d_A). The isomorphism compares the chosen limit
with the limiting kernel cone. -/
noncomputable def sequentialLimitKernelIso (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    limit A ≅ kernel (sequentialDifference A) :=
  limit.isoLimitCone
    ⟨sequentialKernelCone A, sequentialKernelConeIsLimit A⟩

/-- Forward limit-kernel comparison followed by inclusion.

For the comparison e_A : limit A ≅ Ker(d_A), the composite e_A.hom ≫ kernel.ι(d_A) equals L_A
: limit A → P_A. This holds in a preadditive category with countable products and kernels. -/
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

/-- Inverse limit-kernel comparison followed by product coordinates.

For the comparison e_A : limit A ≅ Ker(d_A) in a preadditive category with countable products
and kernels, e_A.inv ≫ L_A = kernel.ι(d_A). Thus the inverse comparison retains the same
product-coordinate inclusion. -/
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

/-- Vanishing of the sequential difference on an inverse limit.

For an inverse tower A with chosen limit in a preadditive category with countable products,
L_A ≫ d_A = 0. Each coordinate vanishes by compatibility of the limit legs with the successor
transition. -/
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

/-- Three-term complex associated to an inverse limit.

For an inverse tower A with chosen limit in a preadditive category with countable products,
form the short complex limit A → P_A → P_A with maps L_A and d_A. Its composite is zero by the
limit compatibility equations. -/
noncomputable def sequentialLimitShortComplex
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] : ShortComplex C :=
  ShortComplex.mk (sequentialLimitToProduct A) (sequentialDifference A)
    (sequentialLimitToProduct_comp_difference A)

/-- First map of the inverse-limit short complex.

For a tower A with chosen limit and countable product in a preadditive category, the first map
of sequentialLimitShortComplex A is L_A : limit A → P_A, determined by the limit projections. -/
@[simp]
theorem sequentialLimitShortComplex_f
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitShortComplex A).f = sequentialLimitToProduct A :=
  rfl

/-- Second map of the inverse-limit short complex.

For a tower A with chosen limit and countable product in a preadditive category, the second
map of sequentialLimitShortComplex A is d_A : P_A → P_A, the identity-minus-shift difference. -/
@[simp]
theorem sequentialLimitShortComplex_g
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    (sequentialLimitShortComplex A).g = sequentialDifference A :=
  rfl

/-- Monic first map in the inverse-limit short complex.

For a tower A with chosen limit in a preadditive category with countable products, the first
map of limit A → P_A → P_A is monic, because its coordinates are the jointly monic limit
projections. -/
noncomputable instance sequentialLimitShortComplex_mono_f
    (A : ℕᵒᵖ ⥤ C) [HasLimit A] :
    Mono (sequentialLimitShortComplex A).f := by
  change Mono (sequentialLimitToProduct A)
  infer_instance

section Cokernels

variable [HasCokernels C]

/-- Concrete sequential lim-one as a difference cokernel.

For an inverse tower A in a preadditive category with countable products and cokernels, define
lim¹ A = Coker(d_A), where d_A has coordinates a_n − t_n(a_{n+1}). This is the concrete
cokernel construction. -/
noncomputable def sequentialLimOne (A : ℕᵒᵖ ⥤ C) : C :=
  cokernel (sequentialDifference A)

/-- Projection to the sequential difference cokernel.

For a tower A in a preadditive category with countable products and cokernels, q_A : P_A →
lim¹ A is cokernel.π(d_A), the quotient map for the identity-minus-shift difference. -/
noncomputable def sequentialLimOneπ (A : ℕᵒᵖ ⥤ C) :
    sequentialProduct A ⟶ sequentialLimOne A :=
  cokernel.π (sequentialDifference A)

/-- Vanishing of the difference followed by the lim-one quotient.

For a tower A in a preadditive category with countable products and cokernels, d_A ≫ q_A = 0,
where q_A : P_A → Coker(d_A) is the sequential lim-one projection. -/
@[reassoc (attr := simp)]
theorem sequentialDifference_comp_limOneπ (A : ℕᵒᵖ ⥤ C) :
    sequentialDifference A ≫ sequentialLimOneπ A = 0 :=
  cokernel.condition _

/-- Map on sequential lim-one induced by a tower morphism.

For α : A → B in a preadditive category with countable products and cokernels, the commuting
difference square induces lim¹(α) : Coker(d_A) → Coker(d_B). It is the cokernel map with both
vertical product maps equal to P(α). -/
noncomputable def sequentialLimOneMap
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOne A ⟶ sequentialLimOne B :=
  cokernel.map (sequentialDifference A) (sequentialDifference B)
    (sequentialProductMap α) (sequentialProductMap α)
    (sequentialDifference_naturality α).symm

/-- Projection equation for a sequential lim-one map.

For a tower map α : A → B, the induced map on the difference cokernels satisfies q_A ≫ lim¹(α)
= P(α) ≫ q_B, with products and cokernels in the preadditive category defined. -/
@[reassoc (attr := simp)]
theorem sequentialLimOneπ_comp_map
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOneπ A ≫ sequentialLimOneMap α =
      sequentialProductMap α ≫ sequentialLimOneπ B := by
  dsimp only [sequentialLimOneπ, sequentialLimOneMap, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- Epimorphism of the sequential lim-one quotient.

For a tower A in a preadditive category with countable products and cokernels, q_A : P_A →
lim¹ A is epic because it is the cokernel projection of d_A. -/
noncomputable instance sequentialLimOneπ_epi (A : ℕᵒᵖ ⥤ C) :
    Epi (sequentialLimOneπ A) := by
  change Epi (cokernel.π (sequentialDifference A))
  infer_instance

/-- Vanishing of sequential lim-one for an epic difference.

For an inverse tower A in a preadditive category with countable products and cokernels, if d_A
: P_A → P_A is epic, then lim¹ A = Coker(d_A) is a zero object. -/
theorem isZero_sequentialLimOne_of_epi
    (A : ℕᵒᵖ ⥤ C) [Epi (sequentialDifference A)] :
    IsZero (sequentialLimOne A) :=
  isZero_cokernel_of_epi (sequentialDifference A)

/-- Identity law for sequential lim-one maps.

For a tower A in a preadditive category with countable products and cokernels, the induced map
lim¹(id_A) is the identity of lim¹ A. -/
@[simp]
theorem sequentialLimOneMap_id (A : ℕᵒᵖ ⥤ C) :
    sequentialLimOneMap (𝟙 A) = 𝟙 (sequentialLimOne A) := by
  apply (cancel_epi (sequentialLimOneπ A)).1
  simp

/-- Composition law for sequential lim-one maps.

For tower maps α : A → B and β : B → D in a preadditive category with countable products and
cokernels, lim¹(α ≫ β) = lim¹(α) ≫ lim¹(β). The equation follows after precomposing with the
epic quotient q_A. -/
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

/-- Functor of sequential difference cokernels.

In a preadditive category with countable products and cokernels, the assignment A ↦ Coker(d_A)
and α ↦ lim¹(α) defines a covariant functor from inverse towers to C. -/
noncomputable def sequentialLimOneFunctor : (ℕᵒᵖ ⥤ C) ⥤ C where
  obj := sequentialLimOne
  map := sequentialLimOneMap
  map_id := sequentialLimOneMap_id
  map_comp := sequentialLimOneMap_comp

/-- Object value of the sequential lim-one functor.

For an inverse tower A in a preadditive category with countable products and cokernels,
sequentialLimOneFunctor.obj A is sequentialLimOne A = Coker(d_A). -/
@[simp]
theorem sequentialLimOneFunctor_obj (A : ℕᵒᵖ ⥤ C) :
    sequentialLimOneFunctor.obj A = sequentialLimOne A :=
  rfl

/-- Morphism value of the sequential lim-one functor.

For a map α : A → B of inverse towers in a preadditive category with countable products and
cokernels, sequentialLimOneFunctor.map α is sequentialLimOneMap α, induced by the product-map
square between d_A and d_B. -/
@[simp]
theorem sequentialLimOneFunctor_map
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialLimOneFunctor.map α = sequentialLimOneMap α :=
  rfl

end Cokernels

end Preadditive

section Abelian

variable [Abelian C] [HasCountableProducts C]

/-- Exactness of a sequential difference followed by its cokernel.

For an inverse tower A in an abelian category with countable products, the sequence P_A → P_A
→ lim¹ A with maps d_A and q_A is exact at its middle product. This is the kernel-image
exactness of a cokernel sequence. -/
theorem sequentialDifference_limOne_exact (A : ℕᵒᵖ ⥤ C) :
    (ShortComplex.mk (sequentialDifference A) (sequentialLimOneπ A)
      (sequentialDifference_comp_limOneπ A)).Exact := by
  simpa only [sequentialLimOne, sequentialLimOneπ] using
    ShortComplex.exact_cokernel (sequentialDifference A)

/-- Exactness of the inverse-limit inclusion and sequential difference.

For an inverse tower A with chosen limit in an abelian category with countable products, the
sequence limit A → P_A → P_A with maps L_A and d_A is exact at P_A. The comparison limit A ≅
Ker(d_A) identifies L_A with the difference kernel inclusion. -/
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
