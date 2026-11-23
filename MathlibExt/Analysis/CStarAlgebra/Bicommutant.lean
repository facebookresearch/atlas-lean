/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

namespace MathlibExt.Analysis.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Matrix as an operator on Euclidean space, via the `toLp` algebra equivalence. -/
private noncomputable def matToOp (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin A

/-- Star on matrices corresponds to adjoint on operators. -/
private theorem matToOp_star (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matToOp n (star A) = LinearMap.adjoint (matToOp n A) := by
  have h1 : star A = Aᴴ := Matrix.star_eq_conjTranspose A
  rw [h1]
  change Matrix.toEuclideanLin Aᴴ = LinearMap.adjoint (Matrix.toEuclideanLin A)
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

/-- `matToOp` preserves multiplication. -/
private theorem matToOp_mul (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    matToOp n (A * B) = matToOp n A * matToOp n B := by
  unfold matToOp
  rw [Matrix.toLpLin_mul, Module.End.mul_eq_comp]

/-- `matToOp` is injective. -/
private theorem matToOp_injective (n : ℕ) : Function.Injective (matToOp n) :=
  Matrix.toEuclideanLin.injective

/-- Amplified block-diagonal action on `m` copies of Euclidean space. -/
private noncomputable def ampOp (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => (matToOp n A).comp (PiLp.projₗ 2 _ i))

/-- Pointwise action of the amplified operator. -/
private theorem ampOp_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    ampOp n m A v i = matToOp n A (v i) := by
  simp [ampOp]

/-- Inner product against the amplified action moves to the starred matrix. -/
private theorem ampOp_inner (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (w v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    ⟪ampOp n m A w, v⟫ = ⟪w, ampOp n m (star A) v⟫ := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ampOp_apply, ampOp_apply, matToOp_star, LinearMap.adjoint_inner_right]

/-- The orthogonal complement of an invariant subspace is invariant. -/
private theorem inv_orthogonal_of_invariant (n m : ℕ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hKs : ∀ A ∈ S, ∀ v ∈ K, ampOp n m (star A) v ∈ K)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ S)
    (w : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) (hw : w ∈ Kᗮ) :
    ampOp n m A w ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [inner_eq_zero_symm, ampOp_inner]
  exact Submodule.inner_left_of_mem_orthogonal (hKs A hA v hv) hw

set_option linter.style.haveILetI false in
/-- The orthogonal projection onto an invariant subspace commutes with the
amplified action. -/
private theorem proj_comm_of_invariant (n m : ℕ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hK : ∀ A ∈ S, ∀ v ∈ K, ampOp n m A v ∈ K)
    (hKs : ∀ A ∈ S, ∀ v ∈ K, ampOp n m (star A) v ∈ K)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ S) :
    K.starProjection.toLinearMap ∘ₗ ampOp n m A
      = ampOp n m A ∘ₗ K.starProjection.toLinearMap := by
  haveI := FiniteDimensional.complete ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n))
  haveI := FiniteDimensional.complete ℂ (↥K)
  haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  have hPz : ∀ z ∈ Kᗮ, K.starProjection.toLinearMap z = 0 := by
    intro z hz
    have h0 : K.starProjection z =
        ((0 : ↥K) : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) := by
      rw [Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz]
    change K.starProjection z = 0
    rw [h0]
    rfl
  have hPy : ∀ y ∈ K, K.starProjection.toLinearMap y = y := by
    intro y hy
    change K.starProjection y = y
    exact Submodule.starProjection_eq_self_iff.mpr hy
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hAy : ampOp n m A y ∈ K := hK A hA y hy
  have hAz : ampOp n m A z ∈ Kᗮ :=
    inv_orthogonal_of_invariant n m S K hKs A hA z hz
  have hPAy : K.starProjection.toLinearMap (ampOp n m A y) = ampOp n m A y :=
    hPy _ hAy
  have hPAz : K.starProjection.toLinearMap (ampOp n m A z) = 0 := hPz _ hAz
  simp only [LinearMap.comp_apply, map_add, map_zero, hPy y hy, hPz z hz, hPAy, hPAz,
    add_zero]

/-- Inclusion of one copy into the amplified space. -/
private noncomputable def ampIncl (n m : ℕ) (j : Fin m) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :=
  (WithLp.linearEquiv 2 ℂ (∀ _ : Fin m, EuclideanSpace ℂ (Fin n))).symm.toLinearMap.comp
    (LinearMap.single ℂ (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j)

/-- Pointwise form of the inclusion. -/
private theorem ampIncl_ofLp (n m : ℕ) (j : Fin m)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    (ampIncl n m j x).ofLp i =
      Pi.single (M := fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j x i :=
  rfl

/-- Amplified operators commute past inclusions. -/
private theorem ampOp_incl (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin m) :
    (ampOp n m A).comp (ampIncl n m j) = (ampIncl n m j).comp (matToOp n A) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ampOp_apply, ampIncl_ofLp,
    ampIncl_ofLp, Pi.single_apply, Pi.single_apply]
  split_ifs with h <;> simp_all

/-- Amplified operators commute past projections. -/
private theorem ampOp_proj (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin m) :
    (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i).comp
        (ampOp n m A) =
      (matToOp n A).comp
        (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change (ampOp n m A v).ofLp i = matToOp n A (v.ofLp i)
  exact ampOp_apply n m A v i

/-- Every amplified vector is the sum of its coordinate inclusions. -/
private theorem sum_ampIncl_proj (n m : ℕ)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    ∑ j, ampIncl n m j
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v) = v := by
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_sum]
  have h := LinearMap.sum_single_apply _ (WithLp.ofLp v)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- Amplification preserves multiplication. -/
private theorem ampOp_mul (n m : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ampOp n m (A * B) = (ampOp n m A).comp (ampOp n m B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [LinearMap.comp_apply, ampOp_apply, ampOp_apply, ampOp_apply, matToOp_mul,
    Module.End.mul_apply]

/-- Amplification preserves one. -/
private theorem ampOp_one (n m : ℕ) : ampOp n m 1 = LinearMap.id := by
  have h1 : matToOp n (1 : Matrix (Fin n) (Fin n) ℂ) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp [matToOp]
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [ampOp_apply, h1, LinearMap.id_apply, LinearMap.id_apply]

/-- Pointwise form of inclusion commutation. -/
private theorem ampOp_incl_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin m)
    (x : EuclideanSpace ℂ (Fin n)) :
    ampOp n m A (ampIncl n m j x) = ampIncl n m j (matToOp n A x) :=
  LinearMap.congr_fun (ampOp_incl n m A j) x

/-- Pointwise form of projection commutation. -/
private theorem ampOp_proj_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin m)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i)
        (ampOp n m A v) =
      matToOp n A
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i) v) :=
  LinearMap.congr_fun (ampOp_proj n m A i) v

/-- The `(i, j)` entry of an amplified operator, as an operator on one copy. -/
private noncomputable def ampEntry (n m : ℕ)
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) (i j : Fin m) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i).comp
    (T.comp (ampIncl n m j))

/-- The matrix realizing an entry operator. -/
private noncomputable def entryMat (n : ℕ)
    (E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.toEuclideanLin.symm E

private theorem matToOp_entryMat (n : ℕ)
    (E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    matToOp n (entryMat n E) = E :=
  Matrix.toEuclideanLin.apply_symm_apply E

/-- Entries inherit commutation with amplified operators. -/
private theorem ampEntry_comm_of_comm (n m : ℕ)
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.comp (ampOp n m A) = (ampOp n m A).comp T) (i j : Fin m) :
    (matToOp n A).comp (ampEntry n m T i j) =
      (ampEntry n m T i j).comp (matToOp n A) := by
  apply LinearMap.ext
  intro x
  simp only [ampEntry, LinearMap.comp_apply]
  have hTx := LinearMap.congr_fun hT ((ampIncl n m j) x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hTx
  rw [← ampOp_proj_apply, ← hTx, ampOp_incl_apply]

/-- Entry matrices lie in the centralizer. -/
private theorem entryMat_mem_centralizer_of_comm (n m : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hT : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      T.comp (ampOp n m A) = (ampOp n m A).comp T) (i j : Fin m) :
    entryMat n (ampEntry n m T i j) ∈
      StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro A hA
  have hAs : star A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    StarMemClass.star_mem hA
  have e1 := ampEntry_comm_of_comm n m T A (hT A hA) i j
  have e2 := ampEntry_comm_of_comm n m T (star A) (hT (star A) hAs) i j
  refine ⟨?_, ?_⟩ <;> apply matToOp_injective n <;>
    rw [matToOp_mul, matToOp_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      matToOp_entryMat] <;>
    assumption

/-- A double-centralizer element commutes, amplified, with anything commuting
with the amplification. -/
private theorem amp_comm_of_mem (n m : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B ∈ StarSubalgebra.centralizer ℂ
      ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ))) :
        Set (Matrix (Fin n) (Fin n) ℂ)))
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hT : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      T.comp (ampOp n m A) = (ampOp n m A).comp T) :
    (ampOp n m B).comp T = T.comp (ampOp n m B) := by
  have eop : ∀ i j : Fin m, (matToOp n B).comp (ampEntry n m T i j) =
      (ampEntry n m T i j).comp (matToOp n B) := by
    intro i j
    have hM := entryMat_mem_centralizer_of_comm n m S T hT i j
    obtain ⟨hM1, -⟩ := (StarSubalgebra.mem_centralizer_iff (R := ℂ)).mp
      (SetLike.mem_coe.mpr hB) _ hM
    have hmul : matToOp n (entryMat n (ampEntry n m T i j) * B) =
        matToOp n (B * entryMat n (ampEntry n m T i j)) := by rw [hM1]
    rw [matToOp_mul, matToOp_mul, matToOp_entryMat] at hmul
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact hmul.symm
  have hTentry : ∀ (j : Fin m) (x : EuclideanSpace ℂ (Fin n)),
      T (ampIncl n m j x) =
        ∑ i, ampIncl n m i ((ampEntry n m T i j) x) := by
    intro j x
    conv_lhs => rw [← sum_ampIncl_proj n m (T (ampIncl n m j x))]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hTv : ∀ (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)),
      T v = ∑ j, T (ampIncl n m j
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v)) := by
    intro v
    conv_lhs => rw [← sum_ampIncl_proj n m v, map_sum]
  have hBv : ∀ (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)),
      ampOp n m B v = ∑ j, ampIncl n m j (matToOp n B
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v)) := by
    intro v
    conv_lhs => rw [← sum_ampIncl_proj n m v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact ampOp_incl_apply n m B j _
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_lhs => rw [hTv, map_sum]
  conv_rhs => rw [hBv, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hTentry]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ampOp_incl_apply]
  congr 1
  exact LinearMap.congr_fun (eop i j) _

/-- Cyclic vector with standard-basis components. -/
private noncomputable def cycVec (n : ℕ) :
    PiLp 2 (fun _ : Fin n => EuclideanSpace ℂ (Fin n)) :=
  WithLp.toLp 2 (fun j => WithLp.toLp 2
    (Pi.single (M := fun _ : Fin n => ℂ) j 1))

private theorem cycVec_ofLp (n : ℕ) (j : Fin n) :
    (cycVec n).ofLp j =
      WithLp.toLp 2 (Pi.single (M := fun _ : Fin n => ℂ) j 1) :=
  rfl

/-- The cyclic subspace generated by the cyclic vector. -/
private noncomputable def cycSub (n : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    Submodule ℂ (PiLp 2 fun _ : Fin n => EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ
    (Set.range (fun s : ↥S => ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)))

/-- The cyclic subspace is invariant under the amplified action. -/
private theorem cycSub_invariant (n : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : C ∈ (S : Set _)) :
    ∀ y ∈ cycSub n S, ampOp n n C y ∈ cycSub n S := by
  have hgen : ∀ y ∈ Set.range
      (fun s : ↥S => ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)),
      ampOp n n C y ∈ cycSub n S := by
    rintro y ⟨s, rfl⟩
    have hmem : C * (s : Matrix (Fin n) (Fin n) ℂ) ∈ (S : Set _) :=
      mul_mem hC s.prop
    have hmul : ampOp n n C (ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)) =
        ampOp n n (C * s) (cycVec n) := by
      rw [ampOp_mul, LinearMap.comp_apply]
    rw [hmul]
    exact Submodule.subset_span ⟨⟨C * s, hmem⟩, rfl⟩
  have hle : cycSub n S ≤ Submodule.comap (ampOp n n C) (cycSub n S) :=
    Submodule.span_le.mpr hgen
  intro y hy
  exact hle hy

/-- **Finite-dimensional bicommutant theorem.** Let $n$ be a natural number and let $S$ be a
unital $*$-subalgebra of the algebra $M_n(\mathbb{C})$ of complex $n \times n$ matrices. Then the
commutant of the commutant of $S$ equals $S$: a matrix commutes with every matrix that commutes
with all elements of $S$ if and only if it lies in $S$.

Source: John von Neumann, "Zur Algebra der Funktionaloperationen und Theorie der normalen
Operatoren", Mathematische Annalen 102 (1930), 370--427, DOI 10.1007/BF01782352. This is the
finite-dimensional specialization: in finite dimension every subspace is closed, so the
strong-operator closure condition of the general theorem is vacuous. -/
theorem bicommutant_finiteDimensional_matrix (n : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    StarSubalgebra.centralizer ℂ
        ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ)) :
          Set (Matrix (Fin n) (Fin n) ℂ))) = S := by
  apply le_antisymm
  · intro B hB
    have hPcomm : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
        (cycSub n S).starProjection.toLinearMap.comp (ampOp n n A) =
          (ampOp n n A).comp (cycSub n S).starProjection.toLinearMap :=
      fun A hA => proj_comm_of_invariant n n _ _
        (fun A hA v hv => cycSub_invariant n S A hA v hv)
        (fun A hA v hv =>
          cycSub_invariant n S (star A) (StarMemClass.star_mem hA) v hv)
        A hA
    have hPB : (ampOp n n B).comp (cycSub n S).starProjection.toLinearMap =
        (cycSub n S).starProjection.toLinearMap.comp (ampOp n n B) :=
      amp_comm_of_mem n n S B hB _ hPcomm
    have hξK : cycVec n ∈ cycSub n S := by
      have h1 : ampOp n n 1 (cycVec n) = cycVec n := by
        rw [ampOp_one, LinearMap.id_apply]
      exact Submodule.subset_span ⟨⟨1, one_mem S⟩, h1⟩
    have hPξ : (cycSub n S).starProjection.toLinearMap (cycVec n) = cycVec n := by
      change (cycSub n S).starProjection (cycVec n) = cycVec n
      exact Submodule.starProjection_eq_self_iff.mpr hξK
    have hBξ : ampOp n n B (cycVec n) ∈ cycSub n S := by
      have hPBξ := LinearMap.congr_fun hPB (cycVec n)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hPξ] at hPBξ
      rw [hPBξ]
      change (cycSub n S).starProjection (ampOp n n B (cycVec n)) ∈ cycSub n S
      exact Submodule.starProjection_apply_mem _ _
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hBξ
    have hc' : (∑ s ∈ c.support,
        (c s) • ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)) =
        ampOp n n B (cycVec n) := hc
    set A₀ : Matrix (Fin n) (Fin n) ℂ :=
      ∑ s ∈ c.support, (c s) • (s : Matrix (Fin n) (Fin n) ℂ) with hA₀def
    have hA₀ : A₀ ∈ S := by
      apply sum_mem
      intro s _
      exact StarSubalgebra.smul_mem S s.prop (c s)
    have hcomp : ∀ j : Fin n, B *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 =
        A₀ *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 := by
      intro j
      have h3 : ∀ M : Matrix (Fin n) (Fin n) ℂ,
          matToOp n M (WithLp.toLp 2 (Pi.single (M := fun _ : Fin n => ℂ) j 1)) =
            WithLp.toLp 2
              (M *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1) := by
        intro M
        change Matrix.toEuclideanLin M _ = _
        exact Matrix.toLpLin_apply 2 2 M _
      have h1j := congrArg (fun w => w.ofLp j) hc'
      rw [WithLp.ofLp_sum, Finset.sum_apply] at h1j
      simp only [WithLp.ofLp_smul, Pi.smul_apply, ampOp_apply, cycVec_ofLp, h3,
        ← WithLp.toLp_sum] at h1j
      -- h1j : toLp (∑ s ∈ support, (c s) • (s *ᵥ single)) = toLp (B *ᵥ single)
      have h5 := congrArg WithLp.ofLp h1j
      have h4 : A₀ *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 =
          ∑ s ∈ c.support, (c s) • ((s : Matrix (Fin n) (Fin n) ℂ) *ᵥ
            Pi.single (M := fun _ : Fin n => ℂ) j 1) := by
        rw [hA₀def, Matrix.sum_mulVec]
        apply Finset.sum_congr rfl
        intro s _
        exact Matrix.smul_mulVec _ _ _
      rw [h4]
      exact h5.symm
    have hBA : B = A₀ := Matrix.ext_of_mulVec_single hcomp
    rw [hBA]
    exact hA₀
  · intro B hB
    have h := StarAlgebra.adjoin_le_centralizer_centralizer ℂ
      (S : Set (Matrix (Fin n) (Fin n) ℂ))
    rw [StarAlgebra.adjoin_eq] at h
    exact h hB

end MathlibExt.Analysis.CStarAlgebra.Bicommutant
