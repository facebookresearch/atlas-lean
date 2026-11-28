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

public import Mathlib.Algebra.Homology.Monoidal
public import MathlibExt.Algebra.Homology.TensorCochainCoherence

universe v u

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

namespace HomologicalComplex

/-!
# Tensor differentials of integer cochain complexes

Let C be preadditive and monoidal, with tensor additive in both variables. For ℤ-indexed cochain
complexes K,L whose degreewise tensor coproducts exist, the total differential on a
(p,q)-summand is d_K⊗id plus (-1)^p id⊗d_L, with p+q=n.

Equivalently the degree-one differential cochain of K⊗L is the sum of the tensor cochains
d_K⊗id_L and id_K⊗d_L. The sign on the second summand is part of the graded tensor operation.
-/

private lemma d₂_eq_up_int (K L : CochainComplex C ℤ) [HasTensor K L]
    (p q n : ℤ) (h : p + (q + 1) = n) :
    mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.up ℤ) p q n =
      p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
        ιTensorObj K L p (q + 1) n h) := by
  have hRel : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  rw [mapBifunctor.d₂_eq K L (curriedTensor C) (ComplexShape.up ℤ) p hRel n h]
  simp

/-- Let C be preadditive and monoidal in object/morphism universes u,v, with tensor additive in both
variables. For ℤ-indexed K,L with their tensor coproducts, p+q=n, the inclusion ι_{p,q,n}
satisfies ι≫d_{n,n+1}=(d_K(p,p+1)⊗id)≫ι_{p+1,q,n+1}+(-1)^p(id⊗d_L(q,q+1))≫ι_{p,q+1,n+1}. -/
public lemma ιTensorObj_comp_d_up_int
    (K L : CochainComplex C ℤ) [HasTensor K L]
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (tensorObj K L).d n (n + 1) =
      ((K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
        ιTensorObj K L (p + 1) q (n + 1) (by omega)) +
      p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
        ιTensorObj K L p (q + 1) (n + 1) (by omega)) := by
  have hD : (tensorObj K L).d n (n + 1) =
      mapBifunctor.D₁ K L (curriedTensor C) (ComplexShape.up ℤ) n (n + 1) +
      mapBifunctor.D₂ K L (curriedTensor C) (ComplexShape.up ℤ) n (n + 1) := by
    rw [mapBifunctor.d_eq]
  have hd₁ : mapBifunctor.d₁ K L (curriedTensor C) (ComplexShape.up ℤ) p q (n + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
        ιTensorObj K L (p + 1) q (n + 1) (by omega) := by
    have hRel : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    have hPi : (p + 1) + q = n + 1 := by omega
    rw [mapBifunctor.d₁_eq K L (curriedTensor C)
      (ComplexShape.up ℤ) hRel q (n + 1) hPi]
    simp
  have hd₂ : mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.up ℤ) p q (n + 1) =
      p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
        ιTensorObj K L p (q + 1) (n + 1) (by omega)) := by
    have hEq : p + (q + 1) = n + 1 := by omega
    rw [d₂_eq_up_int K L p q (n + 1) hEq]
  calc ιTensorObj K L p q n h ≫ (tensorObj K L).d n (n + 1)
      _ = _ := by rw [hD]
      _ = _ := by rw [Preadditive.comp_add]
      _ = mapBifunctor.d₁ K L (curriedTensor C) (ComplexShape.up ℤ) p q (n + 1) +
        mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.up ℤ) p q (n + 1) := by
        rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
      _ = _ := by rw [hd₁, hd₂]

end HomologicalComplex

namespace CochainComplex

/-- Let C be preadditive and monoidal with tensor additive in both variables, and let integer
cochain complexes A,B have all tensor degree coproducts. Their degree-one differential cochains
satisfy d_{A⊗B}=tensor(d_A,id_B)+tensor(id_A,d_B). On left input degree p, the second term
carries (-1)^p. -/
public theorem diff_tensorObj (A B : CochainComplex C ℤ)
    [GradedObject.HasTensor A.X B.X] :
    HomComplex.Cochain.diff (HomologicalComplex.tensorObj A B) =
      Add.add (α := HomComplex.Cochain (HomologicalComplex.tensorObj A B)
          (HomologicalComplex.tensorObj A B) 1)
        (HomComplex.Cochain.tensor (HomComplex.Cochain.diff A)
          (HomComplex.Cochain.ofHom (𝟙 B)))
        (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 A))
          (HomComplex.Cochain.diff B)) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  change (HomologicalComplex.tensorObj A B).d r s =
    (HomComplex.Cochain.tensor (HomComplex.Cochain.diff A)
      (HomComplex.Cochain.ofHom (𝟙 B))).v r s hrs +
    (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 A))
      (HomComplex.Cochain.diff B)).v r s hrs
  rw [HomComplex.Cochain.tensor_v, HomComplex.Cochain.tensor_v]
  have hdecomp : (HomologicalComplex.tensorObj A B).d r s =
      HomologicalComplex.mapBifunctor.D₁ A B (curriedTensor C)
        (ComplexShape.up ℤ) r s +
      HomologicalComplex.mapBifunctor.D₂ A B (curriedTensor C)
        (ComplexShape.up ℤ) r s := rfl
  rw [hdecomp]
  congr 1
  · -- First differential against differential-tensor-identity.
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ hij
    rw [HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.ι_mapBifunctorDesc]
    have hij' : i₁ + i₂ = r := hij
    have hRel : (ComplexShape.up ℤ).Rel i₁ (i₁ + 1) :=
      ComplexShape.up_mk _ _ rfl
    have hpi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⟨i₁ + 1, i₂⟩ = s := by
      have hrs' : r + 1 = s := by omega
      have hpi' : (i₁ + 1) + i₂ = s := by omega
      exact hpi'
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hRel i₂ s hpi]
    rw [HomComplex.Cochain.diff_v]
    -- Normalize `i₂ + 0` to `i₂`: the index sits in dependent positions
    -- (`.v` and `ιTensorObj` proofs), so swap the proofs for hypotheses
    -- (definitionally equal by proof irrelevance), revert them to make the
    -- rewrite motive well-typed, then rewrite.
    have hB : i₂ + 0 = i₂ + 0 := rfl
    have hB_swap : ∀ Q : i₂ + 0 = i₂ + 0,
        (HomComplex.Cochain.ofHom (𝟙 B)).v i₂ (i₂ + 0) Q =
        (HomComplex.Cochain.ofHom (𝟙 B)).v i₂ (i₂ + 0) hB :=
      fun _ => rfl
    rw [hB_swap]
    have hι : (i₁ + 1) + (i₂ + 0) = s := by omega
    -- Swap the `ιTensorObj` proof for `hι`. `simp only` matches the
    -- `tensor_v`-produced application up to defeq (its instances come from a
    -- different context, so `rw`'s syntactic matching fails here).
    have hι_swap : ∀ P : (i₁ + 1) + (i₂ + 0) = s,
        HomologicalComplex.ιTensorObj A B (i₁ + 1) (i₂ + 0) s P =
        HomologicalComplex.ιTensorObj A B (i₁ + 1) (i₂ + 0) s hι :=
      fun _ => rfl
    simp only [hι_swap]
    clear hB_swap hι_swap
    revert hB hι
    -- Occurrence 1 is the `hB`-type LHS (`i₂ + 0` from `i + degree`), which
    -- must stay; occurrences 2-7 are the index positions (including two
    -- hidden ones in implicit `⊗ₘ`/`≫` object arguments) to normalize.
    rw (occs := [2, 3, 4, 5, 6, 7]) [add_zero i₂]
    intro hB hι
    have hId : (HomComplex.Cochain.ofHom (𝟙 B)).v i₂ i₂ hB =
        𝟙 (B.X i₂) := by
      have hproof : (HomComplex.Cochain.ofHom (𝟙 B)).v i₂ i₂ hB =
          (HomComplex.Cochain.ofHom (𝟙 B)).v i₂ i₂ (add_zero i₂) := rfl
      rw [hproof, HomComplex.Cochain.ofHom_v,
        HomologicalComplex.id_f]
    rw [hId]
    simp only [zero_mul, Int.negOnePow_zero, one_smul]
    have hEps : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = 1 := rfl
    rw [hEps, one_smul]
    rw [tensorHom_id]
    rfl
  · -- Second differential against identity-tensor-differential.
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ hij
    rw [HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.ι_mapBifunctorDesc]
    have hij' : i₁ + i₂ = r := hij
    have hRel : (ComplexShape.up ℤ).Rel i₂ (i₂ + 1) :=
      ComplexShape.up_mk _ _ rfl
    have hpi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⟨i₁, i₂ + 1⟩ = s := by
      have hrs' : r + 1 = s := by omega
      have hpi' : i₁ + (i₂ + 1) = s := by omega
      exact hpi'
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ i₁ hRel s hpi]
    rw [HomComplex.Cochain.diff_v]
    -- Normalize `i₁ + 0` to `i₁`, as in the first bullet.
    have hA : i₁ + 0 = i₁ + 0 := rfl
    have hA_swap : ∀ Q : i₁ + 0 = i₁ + 0,
        (HomComplex.Cochain.ofHom (𝟙 A)).v i₁ (i₁ + 0) Q =
        (HomComplex.Cochain.ofHom (𝟙 A)).v i₁ (i₁ + 0) hA :=
      fun _ => rfl
    rw [hA_swap]
    have hι : (i₁ + 0) + (i₂ + 1) = s := by omega
    have hι_swap : ∀ P : (i₁ + 0) + (i₂ + 1) = s,
        HomologicalComplex.ιTensorObj A B (i₁ + 0) (i₂ + 1) s P =
        HomologicalComplex.ιTensorObj A B (i₁ + 0) (i₂ + 1) s hι :=
      fun _ => rfl
    simp only [hι_swap]
    clear hA_swap hι_swap
    revert hA hι
    rw (occs := [2, 3, 4, 5, 6, 7]) [add_zero i₁]
    intro hA hι
    have hId : (HomComplex.Cochain.ofHom (𝟙 A)).v i₁ i₁ hA =
        𝟙 (A.X i₁) := by
      have hproof : (HomComplex.Cochain.ofHom (𝟙 A)).v i₁ i₁ hA =
          (HomComplex.Cochain.ofHom (𝟙 A)).v i₁ i₁ (add_zero i₁) := rfl
      rw [hproof, HomComplex.Cochain.ofHom_v,
        HomologicalComplex.id_f]
    rw [hId]
    simp only [one_mul]
    have hEps : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = i₁.negOnePow := rfl
    rw [hEps]
    rw [id_tensorHom]
    rfl

end CochainComplex
