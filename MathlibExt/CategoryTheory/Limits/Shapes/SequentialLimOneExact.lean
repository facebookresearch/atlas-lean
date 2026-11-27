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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Exact sequences for inverse limits and lim¹

A short exact sequence of inverse sequences in an abelian category with
countable products gives the exact sequence connecting their limits and
concrete sequential lim¹ objects. The additional hypothesis is that the
product of the final component map is epimorphic; countable exact products
supply it uniformly. Each limit comparison requires only the indicated
chosen limits, and the connecting map is natural in short exact rows.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- The countable-product functor on sequential inverse towers. -/
noncomputable def sequentialProductFunctor [HasCountableProducts C] :
    (ℕᵒᵖ ⥤ C) ⥤ C where
  obj A := sequentialProduct A
  map f := sequentialProductMap f
  map_id A := sequentialProductMap_id A
  map_comp f g := (sequentialProductMap_comp f g).symm

/-- The object field of the sequential-product functor. -/
@[simp]
theorem sequentialProductFunctor_obj [HasCountableProducts C]
    (A : ℕᵒᵖ ⥤ C) :
    (sequentialProductFunctor (C := C)).obj A = sequentialProduct A :=
  rfl

/-- The map field of the sequential-product functor. -/
@[simp]
theorem sequentialProductFunctor_map [HasCountableProducts C]
    {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) :
    (sequentialProductFunctor (C := C)).map f = sequentialProductMap f :=
  rfl

section Abelian

variable [Abelian C] [HasCountableProducts C]

/-- The componentwise product of a short complex of inverse towers. -/
noncomputable abbrev sequentialProductShortComplex
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) : ShortComplex C where
  X₁ := sequentialProduct S.X₁
  X₂ := sequentialProduct S.X₂
  X₃ := sequentialProduct S.X₃
  f := sequentialProductMap S.f
  g := sequentialProductMap S.g
  zero := by
    rw [sequentialProductMap_comp]
    apply Pi.hom_ext
    intro n
    simp only [sequentialProductMap_π, zero_comp]
    have h := congrArg (fun q : S.X₁ ⟶ S.X₃ => q.app (op n)) S.zero
    change S.f.app (op n) ≫ S.g.app (op n) = 0 at h
    change Pi.π (fun n : ℕ => S.X₁.obj (op n)) n ≫
      (S.f.app (op n) ≫ S.g.app (op n)) = 0
    rw [h, comp_zero]

/-- The first map of the product short complex is the componentwise product of the first tower
map. -/
@[simp]
theorem sequentialProductShortComplex_f
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    (sequentialProductShortComplex S).f = sequentialProductMap S.f :=
  rfl

/-- The second map of the product short complex is the componentwise product of the second tower
map. -/
@[simp]
theorem sequentialProductShortComplex_g
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    (sequentialProductShortComplex S).g = sequentialProductMap S.g :=
  rfl

private noncomputable def sequentialProductComponentFIsKernel
    {S : ShortComplex (ℕᵒᵖ ⥤ C)} (hS : S.ShortExact) (n : ℕ) :
    IsLimit (KernelFork.ofι (S.f.app (op n)) (by
      have h := congrArg (fun q : S.X₁ ⟶ S.X₃ => q.app (op n)) S.zero
      change S.f.app (op n) ≫ S.g.app (op n) =
        (0 : S.X₁ ⟶ S.X₃).app (op n) at h
      change S.f.app (op n) ≫ S.g.app (op n) = 0 at h
      exact h)) := by
  let e := (evaluation ℕᵒᵖ C).obj (op n)
  have he : (S.map e).ShortExact := hS.map_of_exact e
  dsimp [e, evaluation] at he
  exact he.fIsKernel

/-- The product row of a short exact sequence of towers is short exact when the product of its
final map is epi. -/
theorem sequentialProductShortComplex_shortExact_of_epi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialProductShortComplex S).ShortExact := by
  let _ (n : ℕ) : Mono (S.f.app (op n)) :=
    (hS.map_of_exact ((evaluation ℕᵒᵖ C).obj (op n))).mono_f
  have hmono : Mono (sequentialProductMap S.f) := by
    change Mono (Pi.map (fun n : ℕ => S.f.app (op n)))
    infer_instance
  let _ : Mono (sequentialProductMap S.f) := hmono
  have hExact : (sequentialProductShortComplex S).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι'
      (sequentialProductMap S.f)
      (sequentialProductShortComplex S).zero ?_
    intro X k hk
    change k ≫ sequentialProductMap S.g = 0 at hk
    have hkπ (n : ℕ) :
        (k ≫ Pi.π (fun n : ℕ => S.X₂.obj (op n)) n) ≫
            S.g.app (op n) = 0 := by
      calc
        (k ≫ Pi.π (fun n : ℕ => S.X₂.obj (op n)) n) ≫
              S.g.app (op n) =
            k ≫ (Pi.π (fun n : ℕ => S.X₂.obj (op n)) n ≫
              S.g.app (op n)) := Category.assoc _ _ _
        _ = k ≫ (sequentialProductMap S.g ≫
              Pi.π (fun n : ℕ => S.X₃.obj (op n)) n) := by
            rw [sequentialProductMap_π]
        _ = (k ≫ sequentialProductMap S.g) ≫
              Pi.π (fun n : ℕ => S.X₃.obj (op n)) n :=
            (Category.assoc _ _ _).symm
        _ = 0 := by rw [hk, zero_comp]
    let l (n : ℕ) : X ⟶ S.X₁.obj (op n) :=
      (sequentialProductComponentFIsKernel hS n).lift
        (KernelFork.ofι
          (k ≫ Pi.π (fun n : ℕ => S.X₂.obj (op n)) n) (hkπ n))
    refine ⟨Pi.lift l, ?_⟩
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, sequentialProductMap_π, ← Category.assoc,
      Pi.lift_comp_π]
    exact (sequentialProductComponentFIsKernel hS n).fac
      (KernelFork.ofι
        (k ≫ Pi.π (fun n : ℕ => S.X₂.obj (op n)) n) (hkπ n))
      WalkingParallelPair.zero
  exact ShortComplex.ShortExact.mk' hExact hmono hPg

/-- Countable AB4-star makes the componentwise product of an epi of towers an epimorphism. -/
theorem epi_sequentialProductMap_of_countableAB4Star
    [CountableAB4Star C] {A B : ℕᵒᵖ ⥤ C} (f : A ⟶ B) [Epi f] :
    Epi (sequentialProductMap f) := by
  let F : (Discrete ℕ ⥤ C) ⥤ C := lim
  let _ : F.Additive :=
    { map_add := by
        intro X Y p q
        apply limit.hom_ext
        intro n
        simp [F] }
  let _ : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_preserves_shortExact_right F
      ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1
        inferInstance)
  let p : Discrete.functor (fun n : ℕ => A.obj (op n)) ⟶
      Discrete.functor (fun n : ℕ => B.obj (op n)) :=
    Discrete.natTrans (fun n : Discrete ℕ => f.app (op n.as))
  let _ : Epi p := (NatTrans.epi_iff_epi_app p).2 (fun n => by
    change Epi (f.app (op n.as))
    exact (NatTrans.epi_iff_epi_app f).1 inferInstance (op n.as))
  change Epi (F.map p)
  infer_instance

/-- Countable AB4-star makes the product row of every short exact sequence of towers short exact. -/
theorem sequentialProductShortComplex_shortExact
    [CountableAB4Star C] (S : ShortComplex (ℕᵒᵖ ⥤ C))
    (hS : S.ShortExact) :
    (sequentialProductShortComplex S).ShortExact := by
  let _ : Epi S.g := hS.epi_g
  exact sequentialProductShortComplex_shortExact_of_epi S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

private noncomputable abbrev sequentialDifferenceShortComplexHom
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    sequentialProductShortComplex S ⟶ sequentialProductShortComplex S where
  τ₁ := sequentialDifference S.X₁
  τ₂ := sequentialDifference S.X₂
  τ₃ := sequentialDifference S.X₃
  comm₁₂ := (sequentialDifference_naturality S.f).symm
  comm₂₃ := (sequentialDifference_naturality S.g).symm

@[simp]
private theorem sequentialDifferenceShortComplexHom_π₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    ShortComplex.π₁.map (sequentialDifferenceShortComplexHom S) =
      sequentialDifference S.X₁ :=
  rfl

@[simp]
private theorem sequentialDifferenceShortComplexHom_π₂
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    ShortComplex.π₂.map (sequentialDifferenceShortComplexHom S) =
      sequentialDifference S.X₂ :=
  rfl

@[simp]
private theorem sequentialDifferenceShortComplexHom_π₃
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) :
    ShortComplex.π₃.map (sequentialDifferenceShortComplexHom S) =
      sequentialDifference S.X₃ :=
  rfl

private noncomputable abbrev sequentialLimOneSnakeInputOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) : ShortComplex.SnakeInput C := by
  let P := sequentialProductShortComplex S
  let d := sequentialDifferenceShortComplexHom S
  let hP := sequentialProductShortComplex_shortExact_of_epi S hS hPg
  exact
    { L₀ := kernel d
      L₁ := P
      L₂ := P
      L₃ := cokernel d
      v₀₁ := kernel.ι d
      v₁₂ := d
      v₂₃ := cokernel.π d
      h₀ := kernelIsKernel d
      h₃ := cokernelIsCokernel d
      L₁_exact := hP.exact
      epi_L₁_g := hP.epi_g
      L₂_exact := hP.exact
      mono_L₂_f := hP.mono_f }

private noncomputable def sequentialLimOneSnakeKernelIso₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₁ ≅
      kernel (sequentialDifference S.X₁) := by
  change (ShortComplex.π₁.obj
      (kernel (sequentialDifferenceShortComplexHom S))) ≅
    kernel (ShortComplex.π₁.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso ShortComplex.π₁
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeKernelIso₂
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₂ ≅
      kernel (sequentialDifference S.X₂) := by
  change (ShortComplex.π₂.obj
      (kernel (sequentialDifferenceShortComplexHom S))) ≅
    kernel (ShortComplex.π₂.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso ShortComplex.π₂
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeKernelIso₃
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₃ ≅
      kernel (sequentialDifference S.X₃) := by
  change (ShortComplex.π₃.obj
      (kernel (sequentialDifferenceShortComplexHom S))) ≅
    kernel (ShortComplex.π₃.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso ShortComplex.π₃
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeCokernelIso₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.X₁ ≅
      sequentialLimOne S.X₁ := by
  change (ShortComplex.π₁.obj
      (cokernel (sequentialDifferenceShortComplexHom S))) ≅
    cokernel (ShortComplex.π₁.map (sequentialDifferenceShortComplexHom S))
  exact PreservesCokernel.iso ShortComplex.π₁
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeCokernelIso₂
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.X₂ ≅
      sequentialLimOne S.X₂ := by
  change (ShortComplex.π₂.obj
      (cokernel (sequentialDifferenceShortComplexHom S))) ≅
    cokernel (ShortComplex.π₂.map (sequentialDifferenceShortComplexHom S))
  exact PreservesCokernel.iso ShortComplex.π₂
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeCokernelIso₃
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.X₃ ≅
      sequentialLimOne S.X₃ := by
  change (ShortComplex.π₃.obj
      (cokernel (sequentialDifferenceShortComplexHom S))) ≅
    cokernel (ShortComplex.π₃.map (sequentialDifferenceShortComplexHom S))
  exact PreservesCokernel.iso ShortComplex.π₃
    (sequentialDifferenceShortComplexHom S)

private noncomputable def sequentialLimOneSnakeLimitIso₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₁] :
    limit S.X₁ ≅
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₁ :=
  sequentialLimitKernelIso S.X₁ ≪≫
    (sequentialLimOneSnakeKernelIso₁ S hS hPg).symm

private noncomputable def sequentialLimOneSnakeLimitIso₂
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₂] :
    limit S.X₂ ≅
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₂ :=
  sequentialLimitKernelIso S.X₂ ≪≫
    (sequentialLimOneSnakeKernelIso₂ S hS hPg).symm

private noncomputable def sequentialLimOneSnakeLimitIso₃
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₃] :
    limit S.X₃ ≅
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.X₃ :=
  sequentialLimitKernelIso S.X₃ ≪≫
    (sequentialLimOneSnakeKernelIso₃ S hS hPg).symm

private theorem sequentialLimOneSnakeKernelIso₁_inv_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeKernelIso₁ S hS hPg).inv ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₁ =
      kernel.ι (sequentialDifference S.X₁) := by
  change (PreservesKernel.iso ShortComplex.π₁
      (sequentialDifferenceShortComplexHom S)).inv ≫
      ShortComplex.π₁.map
        (kernel.ι (sequentialDifferenceShortComplexHom S)) =
    kernel.ι (ShortComplex.π₁.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso_inv_ι
    (G := ShortComplex.π₁) (f := sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneSnakeKernelIso₂_inv_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeKernelIso₂ S hS hPg).inv ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₂ =
      kernel.ι (sequentialDifference S.X₂) := by
  change (PreservesKernel.iso ShortComplex.π₂
      (sequentialDifferenceShortComplexHom S)).inv ≫
      ShortComplex.π₂.map
        (kernel.ι (sequentialDifferenceShortComplexHom S)) =
    kernel.ι (ShortComplex.π₂.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso_inv_ι
    (G := ShortComplex.π₂) (f := sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneSnakeKernelIso₃_inv_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeKernelIso₃ S hS hPg).inv ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₃ =
      kernel.ι (sequentialDifference S.X₃) := by
  change (PreservesKernel.iso ShortComplex.π₃
      (sequentialDifferenceShortComplexHom S)).inv ≫
      ShortComplex.π₃.map
        (kernel.ι (sequentialDifferenceShortComplexHom S)) =
    kernel.ι (ShortComplex.π₃.map (sequentialDifferenceShortComplexHom S))
  exact PreservesKernel.iso_inv_ι
    (G := ShortComplex.π₃) (f := sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneSnakeLimitIso₁_hom_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₁] :
    (sequentialLimOneSnakeLimitIso₁ S hS hPg).hom ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₁ =
      sequentialLimitToProduct S.X₁ := by
  change ((sequentialLimitKernelIso S.X₁).hom ≫
      (sequentialLimOneSnakeKernelIso₁ S hS hPg).inv) ≫
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₁ = _
  rw [Category.assoc,
    sequentialLimOneSnakeKernelIso₁_inv_v₀₁ S hS hPg]
  exact sequentialLimitKernelIso_hom_ι S.X₁

private theorem sequentialLimOneSnakeLimitIso₂_hom_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₂] :
    (sequentialLimOneSnakeLimitIso₂ S hS hPg).hom ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₂ =
      sequentialLimitToProduct S.X₂ := by
  change ((sequentialLimitKernelIso S.X₂).hom ≫
      (sequentialLimOneSnakeKernelIso₂ S hS hPg).inv) ≫
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₂ = _
  rw [Category.assoc,
    sequentialLimOneSnakeKernelIso₂_inv_v₀₁ S hS hPg]
  exact sequentialLimitKernelIso_hom_ι S.X₂

private theorem sequentialLimOneSnakeLimitIso₃_hom_v₀₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₃] :
    (sequentialLimOneSnakeLimitIso₃ S hS hPg).hom ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₃ =
      sequentialLimitToProduct S.X₃ := by
  change ((sequentialLimitKernelIso S.X₃).hom ≫
      (sequentialLimOneSnakeKernelIso₃ S hS hPg).inv) ≫
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₃ = _
  rw [Category.assoc,
    sequentialLimOneSnakeKernelIso₃_inv_v₀₁ S hS hPg]
  exact sequentialLimitKernelIso_hom_ι S.X₃

private theorem sequentialLimOneSnakeLimitIso₁_inv_toProduct
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₁] :
    (sequentialLimOneSnakeLimitIso₁ S hS hPg).inv ≫
        sequentialLimitToProduct S.X₁ =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₁ := by
  rw [← sequentialLimOneSnakeLimitIso₁_hom_v₀₁ S hS hPg,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem sequentialLimOneSnakeLimitIso₂_inv_toProduct
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₂] :
    (sequentialLimOneSnakeLimitIso₂ S hS hPg).inv ≫
        sequentialLimitToProduct S.X₂ =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₂ := by
  rw [← sequentialLimOneSnakeLimitIso₂_hom_v₀₁ S hS hPg,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem sequentialLimOneSnakeLimitIso₃_inv_toProduct
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₃] :
    (sequentialLimOneSnakeLimitIso₃ S hS hPg).inv ≫
        sequentialLimitToProduct S.X₃ =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.τ₃ := by
  rw [← sequentialLimOneSnakeLimitIso₃_hom_v₀₁ S hS hPg,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem sequentialLimOneSnake_v₂₃_cokernelIso₁
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₁ ≫
        (sequentialLimOneSnakeCokernelIso₁ S hS hPg).hom =
      sequentialLimOneπ S.X₁ := by
  change ShortComplex.π₁.map
      (cokernel.π (sequentialDifferenceShortComplexHom S)) ≫
      (PreservesCokernel.iso ShortComplex.π₁
        (sequentialDifferenceShortComplexHom S)).hom = _
  exact PreservesCokernel.π_iso_hom ShortComplex.π₁
    (sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneSnake_v₂₃_cokernelIso₂
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₂ ≫
        (sequentialLimOneSnakeCokernelIso₂ S hS hPg).hom =
      sequentialLimOneπ S.X₂ := by
  change ShortComplex.π₂.map
      (cokernel.π (sequentialDifferenceShortComplexHom S)) ≫
      (PreservesCokernel.iso ShortComplex.π₂
        (sequentialDifferenceShortComplexHom S)).hom = _
  exact PreservesCokernel.π_iso_hom ShortComplex.π₂
    (sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneSnake_v₂₃_cokernelIso₃
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₃ ≫
        (sequentialLimOneSnakeCokernelIso₃ S hS hPg).hom =
      sequentialLimOneπ S.X₃ := by
  change ShortComplex.π₃.map
      (cokernel.π (sequentialDifferenceShortComplexHom S)) ≫
      (PreservesCokernel.iso ShortComplex.π₃
        (sequentialDifferenceShortComplexHom S)).hom = _
  exact PreservesCokernel.π_iso_hom ShortComplex.π₃
    (sequentialDifferenceShortComplexHom S)

private theorem sequentialLimOneπ_cokernelIso₁_inv
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOneπ S.X₁ ≫
        (sequentialLimOneSnakeCokernelIso₁ S hS hPg).inv =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₁ := by
  rw [← sequentialLimOneSnake_v₂₃_cokernelIso₁ S hS hPg,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem sequentialLimOneπ_cokernelIso₂_inv
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOneπ S.X₂ ≫
        (sequentialLimOneSnakeCokernelIso₂ S hS hPg).inv =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₂ := by
  rw [← sequentialLimOneSnake_v₂₃_cokernelIso₂ S hS hPg,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem sequentialLimOneπ_cokernelIso₃_inv
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOneπ S.X₃ ≫
        (sequentialLimOneSnakeCokernelIso₃ S hS hPg).inv =
      (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.τ₃ := by
  rw [← sequentialLimOneSnake_v₂₃_cokernelIso₃ S hS hPg,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private noncomputable def sequentialLimOneLimitMapFOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] : limit S.X₁ ⟶ limit S.X₂ :=
  (sequentialLimOneSnakeLimitIso₁ S hS hPg).hom ≫
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.f ≫
    (sequentialLimOneSnakeLimitIso₂ S hS hPg).inv

private noncomputable def sequentialLimOneLimitMapGOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₂] [HasLimit S.X₃] : limit S.X₂ ⟶ limit S.X₃ :=
  (sequentialLimOneSnakeLimitIso₂ S hS hPg).hom ≫
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.g ≫
    (sequentialLimOneSnakeLimitIso₃ S hS hPg).inv

private noncomputable def sequentialLimOneCokernelMapFOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOne S.X₁ ⟶ sequentialLimOne S.X₂ :=
  (sequentialLimOneSnakeCokernelIso₁ S hS hPg).inv ≫
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.f ≫
    (sequentialLimOneSnakeCokernelIso₂ S hS hPg).hom

private noncomputable def sequentialLimOneCokernelMapGOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOne S.X₂ ⟶ sequentialLimOne S.X₃ :=
  (sequentialLimOneSnakeCokernelIso₂ S hS hPg).inv ≫
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.g ≫
    (sequentialLimOneSnakeCokernelIso₃ S hS hPg).hom

/-- The canonical connecting map from the limit of the final tower to the sequential `lim¹` of the
first tower, under the minimal product-epi hypothesis. -/
noncomputable def sequentialLimOneConnectingOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₃] :
    limit S.X₃ ⟶ sequentialLimOne S.X₁ := by
  let P := sequentialProductShortComplex S
  let d : P ⟶ P :=
    { τ₁ := sequentialDifference S.X₁
      τ₂ := sequentialDifference S.X₂
      τ₃ := sequentialDifference S.X₃
      comm₁₂ := (sequentialDifference_naturality S.f).symm
      comm₂₃ := (sequentialDifference_naturality S.g).symm }
  let hP := sequentialProductShortComplex_shortExact_of_epi S hS hPg
  let I : ShortComplex.SnakeInput C :=
    { L₀ := kernel d
      L₁ := P
      L₂ := P
      L₃ := cokernel d
      v₀₁ := kernel.ι d
      v₁₂ := d
      v₂₃ := cokernel.π d
      h₀ := kernelIsKernel d
      h₃ := cokernelIsCokernel d
      L₁_exact := hP.exact
      epi_L₁_g := hP.epi_g
      L₂_exact := hP.exact
      mono_L₂_f := hP.mono_f }
  let k₃ : I.L₀.X₃ ≅ kernel (sequentialDifference S.X₃) := by
    change (ShortComplex.π₃.obj (kernel d)) ≅
      kernel (ShortComplex.π₃.map d)
    exact PreservesKernel.iso ShortComplex.π₃ d
  let l₃ : limit S.X₃ ≅ I.L₀.X₃ :=
    sequentialLimitKernelIso S.X₃ ≪≫ k₃.symm
  let c₁ : I.L₃.X₁ ≅ sequentialLimOne S.X₁ := by
    change (ShortComplex.π₁.obj (cokernel d)) ≅
      cokernel (ShortComplex.π₁.map d)
    exact PreservesCokernel.iso ShortComplex.π₁ d
  exact l₃.hom ≫ I.δ ≫ c₁.hom

/-- The five canonical maps from inverse limits to sequential `lim¹` for a short exact row whose
product final map is epi. -/
noncomputable def sequentialLimOneExactSequenceOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    ComposableArrows C 5 :=
  ComposableArrows.mk₅
    (limMap S.f)
    (limMap S.g)
    (sequentialLimOneConnectingOfProductEpi S hS hPg)
    (sequentialLimOneMap S.f)
    (sequentialLimOneMap S.g)

private theorem sequentialLimOneLimitMapFOfProductEpi_eq
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] :
    sequentialLimOneLimitMapFOfProductEpi S hS hPg = limMap S.f := by
  apply (cancel_mono (sequentialLimitToProduct S.X₂)).1
  simp only [sequentialLimOneLimitMapFOfProductEpi, Category.assoc,
    sequentialLimOneSnakeLimitIso₂_inv_toProduct]
  rw [← (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.comm₁₂]
  rw [← Category.assoc,
    sequentialLimOneSnakeLimitIso₁_hom_v₀₁ S hS hPg]
  exact sequentialLimitToProduct_naturality S.f

private theorem sequentialLimOneLimitMapGOfProductEpi_eq
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₂] [HasLimit S.X₃] :
    sequentialLimOneLimitMapGOfProductEpi S hS hPg = limMap S.g := by
  apply (cancel_mono (sequentialLimitToProduct S.X₃)).1
  simp only [sequentialLimOneLimitMapGOfProductEpi, Category.assoc,
    sequentialLimOneSnakeLimitIso₃_inv_toProduct]
  rw [← (sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₀₁.comm₂₃]
  rw [← Category.assoc,
    sequentialLimOneSnakeLimitIso₂_hom_v₀₁ S hS hPg]
  exact sequentialLimitToProduct_naturality S.g

private theorem sequentialLimOneCokernelMapFOfProductEpi_eq
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOneCokernelMapFOfProductEpi S hS hPg =
      sequentialLimOneMap S.f := by
  apply (cancel_epi (sequentialLimOneπ S.X₁)).1
  change sequentialLimOneπ S.X₁ ≫
      ((sequentialLimOneSnakeCokernelIso₁ S hS hPg).inv ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.f ≫
        (sequentialLimOneSnakeCokernelIso₂ S hS hPg).hom) = _
  rw [← Category.assoc,
    sequentialLimOneπ_cokernelIso₁_inv S hS hPg]
  rw [(sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.comm₁₂_assoc]
  rw [sequentialLimOneSnake_v₂₃_cokernelIso₂ S hS hPg]
  rw [sequentialLimOneπ_comp_map]

private theorem sequentialLimOneCokernelMapGOfProductEpi_eq
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    sequentialLimOneCokernelMapGOfProductEpi S hS hPg =
      sequentialLimOneMap S.g := by
  apply (cancel_epi (sequentialLimOneπ S.X₂)).1
  change sequentialLimOneπ S.X₂ ≫
      ((sequentialLimOneSnakeCokernelIso₂ S hS hPg).inv ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.g ≫
        (sequentialLimOneSnakeCokernelIso₃ S hS hPg).hom) = _
  rw [← Category.assoc,
    sequentialLimOneπ_cokernelIso₂_inv S hS hPg]
  rw [(sequentialLimOneSnakeInputOfProductEpi S hS hPg).v₂₃.comm₂₃_assoc]
  rw [sequentialLimOneSnake_v₂₃_cokernelIso₃ S hS hPg]
  rw [sequentialLimOneπ_comp_map]

private theorem sequentialLimOneConnectingOfProductEpi_eq
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) [HasLimit S.X₃] :
    sequentialLimOneConnectingOfProductEpi S hS hPg =
      (sequentialLimOneSnakeLimitIso₃ S hS hPg).hom ≫
        (sequentialLimOneSnakeInputOfProductEpi S hS hPg).δ ≫
        (sequentialLimOneSnakeCokernelIso₁ S hS hPg).hom := by
  rfl

/-- The first map of the exact sequence is the existing map on chosen inverse limits. -/
theorem sequentialLimOneExactSequenceOfProductEpi_map_zero_one
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 0 1 =
      limMap S.f :=
  rfl

/-- The second map of the exact sequence is the existing map on chosen inverse limits. -/
theorem sequentialLimOneExactSequenceOfProductEpi_map_one_two
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 1 2 =
      limMap S.g :=
  rfl

/-- The middle map of the exact sequence is the canonical connecting map. -/
theorem sequentialLimOneExactSequenceOfProductEpi_map_two_three
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 2 3 =
      sequentialLimOneConnectingOfProductEpi S hS hPg :=
  rfl

/-- The fourth map of the exact sequence is the existing map on sequential `lim¹`. -/
theorem sequentialLimOneExactSequenceOfProductEpi_map_three_four
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 3 4 =
      sequentialLimOneMap S.f :=
  rfl

/-- The final map of the exact sequence is the existing map on sequential `lim¹`. -/
theorem sequentialLimOneExactSequenceOfProductEpi_map_four_five
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 4 5 =
      sequentialLimOneMap S.g :=
  rfl

private noncomputable def sequentialLimOneExactSequenceIsoOfProductEpi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).composableArrows ≅
      sequentialLimOneExactSequenceOfProductEpi S hS hPg :=
  ComposableArrows.isoMk₅
    (sequentialLimOneSnakeLimitIso₁ S hS hPg).symm
    (sequentialLimOneSnakeLimitIso₂ S hS hPg).symm
    (sequentialLimOneSnakeLimitIso₃ S hS hPg).symm
    (sequentialLimOneSnakeCokernelIso₁ S hS hPg)
    (sequentialLimOneSnakeCokernelIso₂ S hS hPg)
    (sequentialLimOneSnakeCokernelIso₃ S hS hPg)
    (by
      change (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.f ≫
          (sequentialLimOneSnakeLimitIso₂ S hS hPg).inv =
        (sequentialLimOneSnakeLimitIso₁ S hS hPg).inv ≫ limMap S.f
      rw [← sequentialLimOneLimitMapFOfProductEpi_eq S hS hPg]
      simp [sequentialLimOneLimitMapFOfProductEpi])
    (by
      change (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₀.g ≫
          (sequentialLimOneSnakeLimitIso₃ S hS hPg).inv =
        (sequentialLimOneSnakeLimitIso₂ S hS hPg).inv ≫ limMap S.g
      rw [← sequentialLimOneLimitMapGOfProductEpi_eq S hS hPg]
      simp [sequentialLimOneLimitMapGOfProductEpi])
    (by
      change (sequentialLimOneSnakeInputOfProductEpi S hS hPg).δ ≫
          (sequentialLimOneSnakeCokernelIso₁ S hS hPg).hom =
        (sequentialLimOneSnakeLimitIso₃ S hS hPg).inv ≫
          sequentialLimOneConnectingOfProductEpi S hS hPg
      rw [sequentialLimOneConnectingOfProductEpi_eq S hS hPg]
      simp)
    (by
      change (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.f ≫
          (sequentialLimOneSnakeCokernelIso₂ S hS hPg).hom =
        (sequentialLimOneSnakeCokernelIso₁ S hS hPg).hom ≫
          sequentialLimOneMap S.f
      rw [← sequentialLimOneCokernelMapFOfProductEpi_eq S hS hPg]
      simp [sequentialLimOneCokernelMapFOfProductEpi])
    (by
      change (sequentialLimOneSnakeInputOfProductEpi S hS hPg).L₃.g ≫
          (sequentialLimOneSnakeCokernelIso₃ S hS hPg).hom =
        (sequentialLimOneSnakeCokernelIso₂ S hS hPg).hom ≫
          sequentialLimOneMap S.g
      rw [← sequentialLimOneCokernelMapGOfProductEpi_eq S hS hPg]
      simp [sequentialLimOneCokernelMapGOfProductEpi])

/-- The canonical six-object sequence is exact under the minimal product-epi hypothesis. -/
theorem sequentialLimOneExactSequenceOfProductEpi_exact
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequenceOfProductEpi S hS hPg).Exact :=
  ComposableArrows.exact_of_iso
    (sequentialLimOneExactSequenceIsoOfProductEpi S hS hPg)
    (sequentialLimOneSnakeInputOfProductEpi S hS hPg).snake_lemma

/-- The first limit map is mono under the minimal product-epi hypothesis; this is the left zero
endpoint of the exact sequence. -/
theorem mono_limMap_f_of_product_epi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g))
    [HasLimit S.X₁] [HasLimit S.X₂] : Mono (limMap S.f) := by
  rw [← sequentialLimOneLimitMapFOfProductEpi_eq S hS hPg]
  let I := sequentialLimOneSnakeInputOfProductEpi S hS hPg
  let hP := sequentialProductShortComplex_shortExact_of_epi S hS hPg
  let _ : Mono I.L₁.f := hP.mono_f
  let _ : Mono I.L₀.f := ShortComplex.SnakeInput.mono_L₀_f I
  change Mono ((sequentialLimOneSnakeLimitIso₁ S hS hPg).hom ≫
    I.L₀.f ≫ (sequentialLimOneSnakeLimitIso₂ S hS hPg).inv)
  infer_instance

/-- The final sequential-lim-one map is epi under the minimal product-epi hypothesis; this is the
right zero endpoint of the exact sequence. -/
theorem epi_sequentialLimOneMap_g_of_product_epi
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    (hPg : Epi (sequentialProductMap S.g)) :
    Epi (sequentialLimOneMap S.g) := by
  rw [← sequentialLimOneCokernelMapGOfProductEpi_eq S hS hPg]
  let I := sequentialLimOneSnakeInputOfProductEpi S hS hPg
  let hP := sequentialProductShortComplex_shortExact_of_epi S hS hPg
  let _ : Epi I.L₂.g := hP.epi_g
  let _ : Epi I.L₃.g := ShortComplex.SnakeInput.epi_L₃_g I
  change Epi ((sequentialLimOneSnakeCokernelIso₂ S hS hPg).inv ≫
    I.L₃.g ≫ (sequentialLimOneSnakeCokernelIso₃ S hS hPg).hom)
  infer_instance

/-- The canonical connecting map when countable products are exact. -/
noncomputable def sequentialLimOneConnecting
    [CountableAB4Star C] (S : ShortComplex (ℕᵒᵖ ⥤ C))
    (hS : S.ShortExact) [HasLimit S.X₃] :
    limit S.X₃ ⟶ sequentialLimOne S.X₁ := by
  let _ : Epi S.g := hS.epi_g
  exact sequentialLimOneConnectingOfProductEpi S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

/-- The canonical six-object exact sequence when countable products are exact. -/
noncomputable def sequentialLimOneExactSequence
    [CountableAB4Star C] (S : ShortComplex (ℕᵒᵖ ⥤ C))
    (hS : S.ShortExact) [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    ComposableArrows C 5 := by
  let _ : Epi S.g := hS.epi_g
  exact sequentialLimOneExactSequenceOfProductEpi S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

/-- The canonical sequence is exact when countable products are exact. -/
theorem sequentialLimOneExactSequence_exact
    [CountableAB4Star C] (S : ShortComplex (ℕᵒᵖ ⥤ C))
    (hS : S.ShortExact) [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃] :
    (sequentialLimOneExactSequence S hS).Exact := by
  let _ : Epi S.g := hS.epi_g
  exact sequentialLimOneExactSequenceOfProductEpi_exact S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

/-- The first limit map is mono when countable products are exact. -/
theorem mono_limMap_f [CountableAB4Star C]
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
    [HasLimit S.X₁] [HasLimit S.X₂] : Mono (limMap S.f) := by
  let _ : Epi S.g := hS.epi_g
  exact mono_limMap_f_of_product_epi S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

/-- The final sequential-lim-one map is epi when countable products are exact. -/
theorem epi_sequentialLimOneMap_g [CountableAB4Star C]
    (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact) :
    Epi (sequentialLimOneMap S.g) := by
  let _ : Epi S.g := hS.epi_g
  exact epi_sequentialLimOneMap_g_of_product_epi S hS
    (epi_sequentialProductMap_of_countableAB4Star S.g)

private noncomputable def sequentialProductShortComplexMap
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (φ : S ⟶ T) :
    sequentialProductShortComplex S ⟶ sequentialProductShortComplex T where
  τ₁ := sequentialProductMap φ.τ₁
  τ₂ := sequentialProductMap φ.τ₂
  τ₃ := sequentialProductMap φ.τ₃
  comm₁₂ := by
    rw [sequentialProductMap_comp, sequentialProductMap_comp, φ.comm₁₂]
  comm₂₃ := by
    rw [sequentialProductMap_comp, sequentialProductMap_comp, φ.comm₂₃]

private theorem sequentialProductShortComplexMap_difference
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (φ : S ⟶ T) :
    sequentialProductShortComplexMap φ ≫
        sequentialDifferenceShortComplexHom T =
      sequentialDifferenceShortComplexHom S ≫
        sequentialProductShortComplexMap φ := by
  apply ShortComplex.hom_ext
  · exact sequentialDifference_naturality φ.τ₁
  · exact sequentialDifference_naturality φ.τ₂
  · exact sequentialDifference_naturality φ.τ₃

private noncomputable def sequentialLimOneSnakeInputHomOfProductEpi
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (hS : S.ShortExact)
    (hT : T.ShortExact) (hPgS : Epi (sequentialProductMap S.g))
    (hPgT : Epi (sequentialProductMap T.g)) (φ : S ⟶ T) :
    sequentialLimOneSnakeInputOfProductEpi S hS hPgS ⟶
      sequentialLimOneSnakeInputOfProductEpi T hT hPgT := by
  let p := sequentialProductShortComplexMap φ
  have w : sequentialDifferenceShortComplexHom S ≫ p =
      p ≫ sequentialDifferenceShortComplexHom T :=
    (sequentialProductShortComplexMap_difference φ).symm
  exact
    { f₀ := kernel.map
        (sequentialDifferenceShortComplexHom S)
        (sequentialDifferenceShortComplexHom T) p p w
      f₁ := p
      f₂ := p
      f₃ := cokernel.map
        (sequentialDifferenceShortComplexHom S)
        (sequentialDifferenceShortComplexHom T) p p w
      comm₀₁ := by
        ext <;> simp [p]
      comm₁₂ := sequentialProductShortComplexMap_difference φ
      comm₂₃ := by
        ext <;> simp [p] }

private theorem sequentialLimOneSnakeInputHom_limit₃
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (hS : S.ShortExact)
    (hT : T.ShortExact) (hPgS : Epi (sequentialProductMap S.g))
    (hPgT : Epi (sequentialProductMap T.g)) (φ : S ⟶ T)
    [HasLimit S.X₃] [HasLimit T.X₃] :
    limMap φ.τ₃ ≫ (sequentialLimOneSnakeLimitIso₃ T hT hPgT).hom =
      (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
        (sequentialLimOneSnakeInputHomOfProductEpi
          hS hT hPgS hPgT φ).f₀.τ₃ := by
  let I := sequentialLimOneSnakeInputOfProductEpi S hS hPgS
  let J := sequentialLimOneSnakeInputOfProductEpi T hT hPgT
  let Φ := sequentialLimOneSnakeInputHomOfProductEpi hS hT hPgS hPgT φ
  let _ : Mono J.v₀₁.τ₃ := ShortComplex.SnakeInput.mono_v₀₁_τ₃ J
  apply (cancel_mono J.v₀₁.τ₃).1
  have hcomm := congrArg ShortComplex.Hom.τ₃ Φ.comm₀₁
  change Φ.f₀.τ₃ ≫ J.v₀₁.τ₃ =
    I.v₀₁.τ₃ ≫ Φ.f₁.τ₃ at hcomm
  calc
    (limMap φ.τ₃ ≫ (sequentialLimOneSnakeLimitIso₃ T hT hPgT).hom) ≫
          J.v₀₁.τ₃ =
        limMap φ.τ₃ ≫
          ((sequentialLimOneSnakeLimitIso₃ T hT hPgT).hom ≫
            J.v₀₁.τ₃) := Category.assoc _ _ _
    _ = limMap φ.τ₃ ≫ sequentialLimitToProduct T.X₃ := by
      rw [sequentialLimOneSnakeLimitIso₃_hom_v₀₁ T hT hPgT]
    _ = sequentialLimitToProduct S.X₃ ≫ sequentialProductMap φ.τ₃ :=
      (sequentialLimitToProduct_naturality φ.τ₃).symm
    _ = ((sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          I.v₀₁.τ₃) ≫ sequentialProductMap φ.τ₃ := by
      rw [sequentialLimOneSnakeLimitIso₃_hom_v₀₁ S hS hPgS]
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          (I.v₀₁.τ₃ ≫ sequentialProductMap φ.τ₃) :=
      Category.assoc _ _ _
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          I.v₀₁.τ₃ ≫ Φ.f₁.τ₃ := rfl
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          (Φ.f₀.τ₃ ≫ J.v₀₁.τ₃) :=
      congrArg (fun q =>
        (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫ q) hcomm.symm
    _ = ((sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫ Φ.f₀.τ₃) ≫
          J.v₀₁.τ₃ := (Category.assoc _ _ _).symm

private theorem sequentialLimOneSnakeInputHom_limOne₁
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (hS : S.ShortExact)
    (hT : T.ShortExact) (hPgS : Epi (sequentialProductMap S.g))
    (hPgT : Epi (sequentialProductMap T.g)) (φ : S ⟶ T) :
    (sequentialLimOneSnakeInputHomOfProductEpi
          hS hT hPgS hPgT φ).f₃.τ₁ ≫
        (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom =
      (sequentialLimOneSnakeCokernelIso₁ S hS hPgS).hom ≫
        sequentialLimOneMap φ.τ₁ := by
  let I := sequentialLimOneSnakeInputOfProductEpi S hS hPgS
  let J := sequentialLimOneSnakeInputOfProductEpi T hT hPgT
  let Φ := sequentialLimOneSnakeInputHomOfProductEpi hS hT hPgS hPgT φ
  let _ : Epi I.v₂₃.τ₁ := ShortComplex.SnakeInput.epi_v₂₃_τ₁ I
  apply (cancel_epi I.v₂₃.τ₁).1
  have hcomm := congrArg ShortComplex.Hom.τ₁ Φ.comm₂₃
  change Φ.f₂.τ₁ ≫ J.v₂₃.τ₁ =
    I.v₂₃.τ₁ ≫ Φ.f₃.τ₁ at hcomm
  rw [← Category.assoc, ← hcomm]
  calc
    (Φ.f₂.τ₁ ≫ J.v₂₃.τ₁) ≫
          (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom =
        Φ.f₂.τ₁ ≫ (J.v₂₃.τ₁ ≫
          (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom) :=
      Category.assoc _ _ _
    _ = sequentialProductMap φ.τ₁ ≫ sequentialLimOneπ T.X₁ := by
      rw [sequentialLimOneSnake_v₂₃_cokernelIso₁ T hT hPgT]
      rfl
    _ = sequentialLimOneπ S.X₁ ≫ sequentialLimOneMap φ.τ₁ :=
      (sequentialLimOneπ_comp_map φ.τ₁).symm
    _ = (I.v₂₃.τ₁ ≫
          (sequentialLimOneSnakeCokernelIso₁ S hS hPgS).hom) ≫
        sequentialLimOneMap φ.τ₁ := by
      rw [sequentialLimOneSnake_v₂₃_cokernelIso₁ S hS hPgS]
    _ = I.v₂₃.τ₁ ≫
        ((sequentialLimOneSnakeCokernelIso₁ S hS hPgS).hom ≫
          sequentialLimOneMap φ.τ₁) := Category.assoc _ _ _

/-- Naturality of the connecting map under the minimal explicit product-epi hypotheses. -/
theorem sequentialLimOneConnectingOfProductEpi_naturality
    {S T : ShortComplex (ℕᵒᵖ ⥤ C)} (hS : S.ShortExact)
    (hT : T.ShortExact) (hPgS : Epi (sequentialProductMap S.g))
    (hPgT : Epi (sequentialProductMap T.g)) (φ : S ⟶ T)
    [HasLimit S.X₃] [HasLimit T.X₃] :
    limMap φ.τ₃ ≫ sequentialLimOneConnectingOfProductEpi T hT hPgT =
      sequentialLimOneConnectingOfProductEpi S hS hPgS ≫
        sequentialLimOneMap φ.τ₁ := by
  let I := sequentialLimOneSnakeInputOfProductEpi S hS hPgS
  let J := sequentialLimOneSnakeInputOfProductEpi T hT hPgT
  let Φ := sequentialLimOneSnakeInputHomOfProductEpi hS hT hPgS hPgT φ
  calc
    limMap φ.τ₃ ≫ sequentialLimOneConnectingOfProductEpi T hT hPgT =
        (limMap φ.τ₃ ≫
          (sequentialLimOneSnakeLimitIso₃ T hT hPgT).hom) ≫
            J.δ ≫ (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom := by
      rw [sequentialLimOneConnectingOfProductEpi_eq T hT hPgT]
      simp only [Category.assoc]
      rfl
    _ = ((sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫ Φ.f₀.τ₃) ≫
          J.δ ≫ (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom := by
      rw [sequentialLimOneSnakeInputHom_limit₃ hS hT hPgS hPgT φ]
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          (Φ.f₀.τ₃ ≫ J.δ) ≫
            (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom := by
      simp only [Category.assoc]
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫
          (I.δ ≫ Φ.f₃.τ₁) ≫
            (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom := by
      rw [← I.naturality_δ Φ]
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫ I.δ ≫
          (Φ.f₃.τ₁ ≫
            (sequentialLimOneSnakeCokernelIso₁ T hT hPgT).hom) := by
      simp only [Category.assoc]
    _ = (sequentialLimOneSnakeLimitIso₃ S hS hPgS).hom ≫ I.δ ≫
          ((sequentialLimOneSnakeCokernelIso₁ S hS hPgS).hom ≫
            sequentialLimOneMap φ.τ₁) := by
      rw [sequentialLimOneSnakeInputHom_limOne₁ hS hT hPgS hPgT φ]
    _ = sequentialLimOneConnectingOfProductEpi S hS hPgS ≫
          sequentialLimOneMap φ.τ₁ := by
      rw [sequentialLimOneConnectingOfProductEpi_eq S hS hPgS]
      simp only [Category.assoc]
      rfl

/-- Naturality of the connecting map when countable products are exact. -/
theorem sequentialLimOneConnecting_naturality
    [CountableAB4Star C] {S T : ShortComplex (ℕᵒᵖ ⥤ C)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    [HasLimit S.X₃] [HasLimit T.X₃] :
    limMap φ.τ₃ ≫ sequentialLimOneConnecting T hT =
      sequentialLimOneConnecting S hS ≫ sequentialLimOneMap φ.τ₁ := by
  let _ : Epi S.g := hS.epi_g
  let _ : Epi T.g := hT.epi_g
  dsimp only [sequentialLimOneConnecting]
  exact sequentialLimOneConnectingOfProductEpi_naturality hS hT
    (epi_sequentialProductMap_of_countableAB4Star S.g)
    (epi_sequentialProductMap_of_countableAB4Star T.g) φ

end Abelian

end CategoryTheory.Limits

end
