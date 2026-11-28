/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.Grp.Abelian
public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexReducedEquivalence

/-!
# The two-sided annihilator Hom cochain complex

Let D be preadditive and η : U → C, ε : A → V maps of integer cochain complexes. The homogeneous
cochains θ killed by η-precomposition and ε-postcomposition form a subcomplex of Hom(C,A). Its
differential is the restriction of ∂θ=d_A ∘ θ-(-1)^n θ ∘ d_C in degree n.

If D has kernels and cokernels, reconstruction through coker η and ker ε is an isomorphism of
cochain complexes Hom(coker η,ker ε) ≅ Ann(η,ε), hence induces an isomorphism on cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex.Cochain

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {U C A V : CochainComplex D ℤ}

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. For all integers n,m, the Hom differential sends Annⁿ(η,ε) into
Annᵐ(η,ε). In the adjacent degree m=n+1 it is ∂θ=d_A ∘ θ-(-1)^n θ ∘ d_C; nonadjacent
differentials are zero. -/
theorem δ_mem_annihilator (η : U ⟶ C) (ε : A ⟶ V) (n m : ℤ)
    (τ : Cochain C A n) (hτ : τ ∈ annihilator η ε n) :
    δ n m τ ∈ annihilator η ε m := by
  rw [mem_annihilator] at hτ ⊢
  constructor
  · calc
      (ofHom η).comp (δ n m τ) (zero_add m) =
          δ n m ((ofHom η).comp τ (zero_add n)) :=
        (δ_ofHom_comp η τ m).symm
      _ = 0 := by rw [hτ.1, δ_zero]
  · calc
      (δ n m τ).comp (ofHom ε) (add_zero m) =
          δ n m (τ.comp (ofHom ε) (add_zero n)) :=
        (δ_comp_ofHom τ ε m).symm
      _ = 0 := by rw [hτ.2, δ_zero]

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. The subgroups Annⁿ(η,ε), with the restricted signed Hom
differential, form an integer cochain complex of abelian groups. No kernels or cokernels of D
are needed. -/
def annihilatorComplex (η : U ⟶ C) (ε : A ⟶ V) :
    CochainComplex AddCommGrpCat.{v} ℤ := by
  let annDelta (n m : ℤ) : annihilator η ε n →+ annihilator η ε m :=
    { toFun τ := ⟨δ n m τ.val, δ_mem_annihilator η ε n m τ.val τ.property⟩
      map_zero' := by
        apply Subtype.ext
        exact δ_zero n m
      map_add' τ σ := by
        apply Subtype.ext
        exact δ_add n m τ.val σ.val }
  refine
    { X := fun n => AddCommGrpCat.of (annihilator η ε n)
      d := fun n m => AddCommGrpCat.ofHom (annDelta n m)
      shape := ?_
      d_comp_d' := ?_ }
  · intro n m hnm
    apply AddCommGrpCat.ext
    intro τ
    apply Subtype.ext
    change δ n m τ.val = 0
    exact δ_shape n m hnm τ.val
  · intro n m k _ _
    apply AddCommGrpCat.ext
    intro τ
    apply Subtype.ext
    change δ m k (δ n m τ.val) = 0
    exact δ_δ n m k τ.val

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. For θ in degree n and any integer m, the degree-(n,m)
differential of the annihilator complex has underlying cochain δ(n,m,θ). Thus it retains the
signed Hom differential in every degree. -/
theorem annihilatorComplex_d_apply (η : U ⟶ C) (ε : A ⟶ V)
    (n m : ℤ) (τ : annihilator η ε n) :
    (((annihilatorComplex η ε).d n m) τ : annihilator η ε m).val = δ n m τ.val :=
  rfl

end CochainComplex.HomComplex.Cochain

end

namespace CochainComplex.HomComplex.Cochain

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [HasKernels D] [HasCokernels D]
variable {U C A V : CochainComplex D ℤ}

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. The degreewise reconstruction maps form an isomorphism of
cochain complexes Hom(coker η,ker ε) ≅ Ann(η,ε), compatible with the signed Hom differentials. -/
def cokernelKernelHomComplexIso (η : U ⟶ C) (ε : A ⟶ V) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    CochainComplex.HomComplex (cokernel η) (kernel ε) ≅ annihilatorComplex η ε := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  let reconstruct (n : ℤ) (θ : Cochain (cokernel η) (kernel ε) n) : Cochain C A n :=
    ((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
      (ofHom (kernel.ι ε)) (add_zero n)
  have hδ (n m : ℤ) (θ : Cochain (cokernel η) (kernel ε) n) :
      δ n m (reconstruct n θ) = reconstruct m (δ n m θ) := by
    change δ n m
        (((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
          (ofHom (kernel.ι ε)) (add_zero n)) =
      ((ofHom (cokernel.π η)).comp (δ n m θ) (zero_add m)).comp
        (ofHom (kernel.ι ε)) (add_zero m)
    rw [δ_comp_ofHom, δ_ofHom_comp]
  let degreeEquiv (n : ℤ) :
      Cochain (cokernel η) (kernel ε) n ≃+ ↥(annihilator η ε n) :=
    cokernelKernelAddEquiv η ε n
  let component (n : ℤ) :
      (CochainComplex.HomComplex (cokernel η) (kernel ε)).X n ≅
        (annihilatorComplex η ε).X n := by
    change AddCommGrpCat.of (Cochain (cokernel η) (kernel ε) n) ≅
      AddCommGrpCat.of ↥(annihilator η ε n)
    exact (degreeEquiv n).toAddCommGrpIso
  refine HomologicalComplex.Hom.isoOfComponents component ?_
  intro n m _
  apply AddCommGrpCat.ext
  intro θ
  apply Subtype.ext
  change δ n m ((degreeEquiv n θ).val) = (degreeEquiv m (δ n m θ)).val
  have hn : (degreeEquiv n θ).val = reconstruct n θ := by
    change (cokernelKernelAddEquiv η ε n θ).val =
      ((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
        (ofHom (kernel.ι ε)) (add_zero n)
    exact cokernelKernelAddEquiv_apply η ε n θ
  have hm : (degreeEquiv m (δ n m θ)).val = reconstruct m (δ n m θ) := by
    change (cokernelKernelAddEquiv η ε m (δ n m θ)).val =
      ((ofHom (cokernel.π η)).comp (δ n m θ) (zero_add m)).comp
        (ofHom (kernel.ι ε)) (add_zero m)
    exact cokernelKernelAddEquiv_apply η ε m (δ n m θ)
  exact (congrArg (δ n m) hn).trans ((hδ n m θ).trans hm.symm)

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. In every degree n, the forward component of the Hom complex
isomorphism sends θ′ to i_ε ∘ θ′ ∘ π_η as a cochain from C to A. -/
theorem cokernelKernelHomComplexIso_hom_f_apply
    (η : U ⟶ C) (ε : A ⟶ V) (n : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∀ θ : Cochain (cokernel η) (kernel ε) n,
      (((cokernelKernelHomComplexIso η ε).hom.f n) θ : annihilator η ε n).val =
        ((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
          (ofHom (kernel.ι ε)) (add_zero n) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  intro θ
  change (cokernelKernelAddEquiv η ε n θ).val =
    ((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
      (ofHom (kernel.ι ε)) (add_zero n)
  exact cokernelKernelAddEquiv_apply η ε n θ

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. In every degree n, the inverse component sends θ ∈ Annⁿ(η,ε)
to its unique homogeneous factor θ′ : coker η → ker ε. It agrees with the inverse additive
reconstruction equivalence. -/
theorem cokernelKernelHomComplexIso_inv_f_apply
    (η : U ⟶ C) (ε : A ⟶ V) (n : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    ∀ τ : annihilator η ε n,
      ((cokernelKernelHomComplexIso η ε).inv.f n) τ =
        (cokernelKernelAddEquiv η ε n).symm τ := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  intro τ
  change (cokernelKernelAddEquiv η ε n).symm τ = _
  rfl

end

end CochainComplex.HomComplex.Cochain

namespace CochainComplex.HomComplex.Cochain

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [HasKernels D] [HasCokernels D]
variable {U C A V : CochainComplex D ℤ}

/-- Let D be preadditive and let U,C,A,V be integer cochain complexes, with complex maps η : U → C
and ε : A → V. For n ∈ ℤ, Annⁿ(η,ε) consists of homogeneous cochains θ : C → A of degree n
satisfying θ ∘ η=0 and ε ∘ θ=0. Assume D has kernels and cokernels, so the complexes coker(η)
and ker(ε) are computed degreewise. For each integer n, reconstruction induces a canonical
isomorphism Hⁿ Hom(coker η,ker ε) ≅ Hⁿ Ann(η,ε), by the cochain-complex isomorphism of these
abelian-group complexes. -/
def cokernelKernelCohomologyIso (η : U ⟶ C) (ε : A ⟶ V) (n : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    (CochainComplex.HomComplex (cokernel η) (kernel ε)).homology n ≅
      (annihilatorComplex η ε).homology n := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  dsimp only
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
    (ComplexShape.up ℤ) n).mapIso (cokernelKernelHomComplexIso η ε)

end

end CochainComplex.HomComplex.Cochain
