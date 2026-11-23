/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology
public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced

/-!
# Base cases for relative singular homology

With coefficients in an abelian category admitting the required coproducts,
relative singular homology agrees with absolute homology for an empty subspace.
Degree zero vanishes when the ambient space is path connected and the subspace
is nonempty. For a contractible ambient space, relative homology in degree `n +
1` is identified with reduced homology of the subspace in degree `n`.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Canonical isomorphism `H_n(X;R) ≅ H_n((X,∅);R)` for a pair with empty subspace. -/
noncomputable def singularHomologyEmptyPairObjIso (R : C) (P : TopPair.{w}) [IsEmpty P.snd]
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj P.fst ≅
      (relativeSingularHomologyFunctor C R n).obj P :=
  HomologicalComplex.homologyMapIso (asIso ((singularPairShortComplexFunctor C R).obj P).g) n

@[simp]
lemma singularHomologyEmptyPairObjIso_hom (R : C) (P : TopPair.{w}) [IsEmpty P.snd]
    (n : ℕ) :
    (singularHomologyEmptyPairObjIso C R P n).hom =
      HomologicalComplex.homologyMap ((singularPairShortComplexFunctor C R).obj P).g n :=
  rfl

-- Private auxiliary: `H₀(A) ⟶ H₀(X)` is epi when `A` is nonempty and `X` path connected.
private theorem epi_singularHomologyZero_map_of_nonempty_of_pathConnected
    (R : C) (P : TopPair.{w}) (hA : Nonempty P.snd) [PathConnectedSpace P.fst] :
    Epi ((singularHomologyFunctor C 0).obj R |>.map P.map) := by
  classical
  obtain ⟨a⟩ := hA
  let pointToA : TopCat.of PUnit.{w + 1} ⟶ P.snd :=
    TopCat.ofHom ⟨fun _ => a, continuous_const⟩
  let pointToX : TopCat.of PUnit.{w + 1} ⟶ P.fst :=
    pointToA ≫ P.map
  have hComp :
      ((singularHomologyFunctor C (0 : ℕ)).obj R).map pointToA ≫
        ((singularHomologyFunctor C (0 : ℕ)).obj R).map P.map =
      ((singularHomologyFunctor C (0 : ℕ)).obj R).map pointToX := by
    rw [← Functor.map_comp]
  have : IsIso (P.fst.singularHomology₀ε (C := C) R) :=
    inferInstance
  have : IsIso ((TopCat.of PUnit.{w + 1}).singularHomology₀ε (C := C) R) :=
    inferInstance
  have hNat :
      ((singularHomologyFunctor C 0).obj R).map pointToX ≫
        P.fst.singularHomology₀ε R =
      (TopCat.of PUnit.{w + 1}).singularHomology₀ε R :=
    TopCat.singularHomologyMap_comp_singularHomology₀ε pointToX R
  have hIso_pointToX : IsIso ((singularHomologyFunctor C 0).obj R |>.map pointToX) := by
    have hEq : ((singularHomologyFunctor C 0).obj R).map pointToX =
        (TopCat.of PUnit.{w + 1}).singularHomology₀ε R ≫
          inv (P.fst.singularHomology₀ε R) := by
      calc ((singularHomologyFunctor C 0).obj R).map pointToX
          = ((singularHomologyFunctor C 0).obj R).map pointToX ≫ 𝟙 _ := by
            rw [Category.comp_id]
        _ = ((singularHomologyFunctor C 0).obj R).map pointToX ≫
            (P.fst.singularHomology₀ε R ≫ inv (P.fst.singularHomology₀ε R)) := by
            rw [IsIso.hom_inv_id]
        _ = (((singularHomologyFunctor C 0).obj R).map pointToX ≫
            P.fst.singularHomology₀ε R) ≫ inv (P.fst.singularHomology₀ε R) := by
            rw [Category.assoc]
        _ = (TopCat.of PUnit.{w + 1}).singularHomology₀ε R ≫
            inv (P.fst.singularHomology₀ε R) := by
            rw [hNat]
    rw [hEq]
    infer_instance
  have hEpi_pointToX : Epi ((singularHomologyFunctor C 0).obj R |>.map pointToX) :=
    inferInstance
  have hEpi : Epi (((singularHomologyFunctor C 0).obj R).map P.map) :=
    epi_of_epi_fac hComp
  exact hEpi

/-- If the subspace is nonempty and the ambient space is path connected,
relative `H₀` vanishes. -/
theorem isZero_relativeSingularHomologyZero_of_pathConnectedSpace
    (R : C) (P : TopPair.{w}) (hA : Nonempty P.snd) [PathConnectedSpace P.fst] :
    IsZero ((relativeSingularHomologyFunctor C R 0).obj P) := by
  classical
  let S := (singularPairShortComplexFunctor C R).obj P
  have hSE : S.ShortExact :=
    singularPairShortComplex_shortExact C R P
  have hEpi_f : Epi (HomologicalComplex.homologyMap S.f 0) := by
    change Epi (((singularHomologyFunctor C 0).obj R).map P.map)
    exact epi_singularHomologyZero_map_of_nonempty_of_pathConnected C R P hA
  have hNoRel : ∀ j : ℕ, ¬ (ComplexShape.down ℕ).Rel (0 : ℕ) j := by
    intro j hj
    simp [ComplexShape.down] at hj
  have hEpi_g_chain : Epi S.g :=
    hSE.epi_g
  have hEpi_hom_g : Epi (HomologicalComplex.homologyMap S.g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 hNoRel
  have hfg_zero : HomologicalComplex.homologyMap S.f 0 ≫
      HomologicalComplex.homologyMap S.g 0 = 0 := by
    have hZero : S.f ≫ S.g = 0 := S.zero
    calc HomologicalComplex.homologyMap S.f 0 ≫ HomologicalComplex.homologyMap S.g 0
          = HomologicalComplex.homologyMap (S.f ≫ S.g) 0 := by
            rw [HomologicalComplex.homologyMap_comp]
        _ = HomologicalComplex.homologyMap (0 : S.X₁ ⟶ S.X₃) 0 := by
            rw [hZero]
        _ = 0 := by
            rw [HomologicalComplex.homologyMap_zero]
  have h_g_zero : HomologicalComplex.homologyMap S.g 0 = 0 := by
    have h0 : HomologicalComplex.homologyMap S.f 0 ≫ HomologicalComplex.homologyMap S.g 0 =
      HomologicalComplex.homologyMap S.f 0 ≫ 0 := by
      rw [hfg_zero, comp_zero]
    exact (cancel_epi (HomologicalComplex.homologyMap S.f 0)).mp h0
  -- bind epi proof explicitly before installing as local instance
  have hEpiZero : Epi (0 : S.X₂.homology 0 ⟶ S.X₃.homology 0) := by
    rw [← h_g_zero]
    exact hEpi_hom_g
  have hZeroX₃ : IsZero (S.X₃.homology 0) :=
    IsZero.of_epi_zero (S.X₂.homology 0) (S.X₃.homology 0)
  -- `relativeSingularHomologyFunctor` is definitionally `S.X₃.homology`
  change IsZero (S.X₃.homology 0) at *
  exact hZeroX₃

set_option backward.isDefEq.respectTransparency false in
/-- Canonical iso `H_{n+1}(X,A) ≅ ker(H_n(A) → H_n(X))` when `X` contractible.

For `S = C(A) → C(X) → C(X,A)`, `H_{n+1}(X)=0` gives `δ` mono by `mono_δ`.
Exactness at `H_n(A)` is `homology_exact₁`, so `δ` is a kernel of
`H_n(A) → H_n(X)`. Comparison of the two kernel limits via
`conePointUniqueUpToIso` yields the canonical iso. -/
noncomputable def relativeSingularHomologyKernelIsoOfContractibleAmbient
    (R : C) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    (relativeSingularHomologyFunctor C R (n + 1)).obj P ≅
      kernel (((singularHomologyFunctor C n).obj R).map P.map) := by
  classical
  let S := (singularPairShortComplexFunctor C R).obj P
  have hSE : S.ShortExact := singularPairShortComplex_shortExact C R P
  have hZero : IsZero (S.X₂.homology (n + 1)) :=
    isZero_singularHomology_of_contractible C R (n + 1) (Nat.succ_ne_zero n) (↥P.fst)
  have hMono : Mono (hSE.δ (n + 1) n (by simp)) :=
    hSE.mono_δ (n + 1) n (by simp) hZero
  have hExact : (ShortComplex.mk (hSE.δ (n + 1) n (by simp))
      (HomologicalComplex.homologyMap S.f n) (hSE.δ_comp (n + 1) n (by simp))).Exact :=
    hSE.homology_exact₁ (n + 1) n (by simp)
  have : Mono (hSE.δ (n + 1) n (by simp)) := hMono
  let c₁ : KernelFork (((singularHomologyFunctor C n).obj R).map P.map) :=
    KernelFork.ofι (hSE.δ (n + 1) n (by simp)) (hSE.δ_comp (n + 1) n (by simp))
  let c₂ : KernelFork (((singularHomologyFunctor C n).obj R).map P.map) :=
    KernelFork.ofι (kernel.ι (((singularHomologyFunctor C n).obj R).map P.map))
      (kernel.condition (((singularHomologyFunctor C n).obj R).map P.map))
  let h₁ : IsLimit c₁ := hExact.fIsKernel
  let h₂ : IsLimit c₂ := kernelIsKernel (((singularHomologyFunctor C n).obj R).map P.map)
  exact IsLimit.conePointUniqueUpToIso (s := c₁) (t := c₂) h₁ h₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem relativeSingularHomologyKernelIsoOfContractibleAmbient_hom_ι
    (R : C) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    (relativeSingularHomologyKernelIsoOfContractibleAmbient C R P n).hom ≫
      kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) =
      (relativeSingularBoundary C R n).app P := by
  classical
  let S := (singularPairShortComplexFunctor C R).obj P
  have hSE : S.ShortExact := singularPairShortComplex_shortExact C R P
  have hZero : IsZero (S.X₂.homology (n + 1)) :=
    isZero_singularHomology_of_contractible C R (n + 1) (Nat.succ_ne_zero n) (↥P.fst)
  have hMono : Mono (hSE.δ (n + 1) n (by simp)) :=
    hSE.mono_δ (n + 1) n (by simp) hZero
  have hExact : (ShortComplex.mk (hSE.δ (n + 1) n (by simp))
      (HomologicalComplex.homologyMap S.f n) (hSE.δ_comp (n + 1) n (by simp))).Exact :=
    hSE.homology_exact₁ (n + 1) n (by simp)
  have : Mono (hSE.δ (n + 1) n (by simp)) := hMono
  dsimp [relativeSingularHomologyKernelIsoOfContractibleAmbient,
    relativeSingularBoundary]
  have hComp := IsLimit.conePointUniqueUpToIso_hom_comp
    (t := KernelFork.ofι (kernel.ι (((singularHomologyFunctor C n).obj R).map P.map))
      (kernel.condition (((singularHomologyFunctor C n).obj R).map P.map)))
    hExact.fIsKernel
    (kernelIsKernel (((singularHomologyFunctor C n).obj R).map P.map))
    WalkingParallelPair.zero
  simpa using hComp

/-- Relative `H_{n+1}(X,A)` is reduced `H̃_n(A)` when `X` contractible, via the
kernel iso composed with the accepted reduced-kernel iso. -/
noncomputable def relativeSingularHomologyReducedIsoOfContractibleAmbient
    (R : C) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    (relativeSingularHomologyFunctor C R (n + 1)).obj P ≅
      reducedSingularHomology C R n P.snd :=
  relativeSingularHomologyKernelIsoOfContractibleAmbient C R P n ≪≫
    (reducedSingularHomologyKernelIsoOfContractibleTarget C R n P.map).symm

@[reassoc (attr := simp)]
theorem relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_ι
    (R : C) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
      (reducedSingularHomologyι C R n).app P.snd =
      (relativeSingularBoundary C R n).app P := by
  classical
  let eK := relativeSingularHomologyKernelIsoOfContractibleAmbient C R P n
  let eR := reducedSingularHomologyKernelIsoOfContractibleTarget C R n P.map
  have hK : eK.hom ≫ kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) =
      (relativeSingularBoundary C R n).app P :=
    relativeSingularHomologyKernelIsoOfContractibleAmbient_hom_ι C R P n
  have hR : eR.hom ≫ kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) =
      (reducedSingularHomologyι C R n).app P.snd :=
    reducedSingularHomologyKernelIsoOfContractibleTarget_hom_ι C R n P.map
  have hSymm : eR.symm.hom ≫ (reducedSingularHomologyι C R n).app P.snd =
      kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) := by
    calc eR.symm.hom ≫ (reducedSingularHomologyι C R n).app P.snd
        = eR.inv ≫ (reducedSingularHomologyι C R n).app P.snd := rfl
      _ = eR.inv ≫ (eR.hom ≫ kernel.ι (((singularHomologyFunctor C n).obj R).map P.map)) := by
          rw [← hR]
      _ = (eR.inv ≫ eR.hom) ≫ kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) := by
          rw [Category.assoc]
      _ = 𝟙 _ ≫ kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) := by rw [eR.inv_hom_id]
      _ = kernel.ι (((singularHomologyFunctor C n).obj R).map P.map) := by rw [Category.id_comp]
  have hEq : (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom =
      eK.hom ≫ eR.symm.hom := by
    simp [relativeSingularHomologyReducedIsoOfContractibleAmbient, eK, eR]
  rw [hEq, Category.assoc, hSymm, hK]

/-- Naturality in the pair of the contractible-ambient comparison with
reduced subspace homology. -/
theorem relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) {P Q : TopPair.{w}}
    [ContractibleSpace P.fst] [ContractibleSpace Q.fst]
    (f : P ⟶ Q) (n : ℕ) :
    (relativeSingularHomologyFunctor C R (n + 1)).map f ≫
        (relativeSingularHomologyReducedIsoOfContractibleAmbient
          C R Q n).hom =
      (relativeSingularHomologyReducedIsoOfContractibleAmbient
          C R P n).hom ≫
        (reducedSingularHomologyFunctor C R n).map
          (TopPair.Hom.snd f) := by
  have : Mono ((reducedSingularHomologyι C R n).app Q.snd) := by
    rw [(reducedSingularHomologyObjIso_hom_ι C R n Q.snd).symm]
    infer_instance
  have hProj : TopPair.proj₂.map f = TopPair.Hom.snd f :=
    MorphismProperty.Arrow.forget_comp_leftFunc_map
      TopCat.isEmbedding ⊤ ⊤ f
  have hBoundary :
      (relativeSingularHomologyFunctor C R (n + 1)).map f ≫
          (relativeSingularBoundary C R n).app Q =
        (relativeSingularBoundary C R n).app P ≫
          ((singularHomologyFunctor C n).obj R).map
            (TopPair.Hom.snd f) := by
    rw [← hProj]
    exact (relativeSingularBoundary C R n).naturality f
  have hReduced :
      (reducedSingularHomologyFunctor C R n).map
            (TopPair.Hom.snd f) ≫
          (reducedSingularHomologyι C R n).app Q.snd =
        (reducedSingularHomologyι C R n).app P.snd ≫
          ((singularHomologyFunctor C n).obj R).map
            (TopPair.Hom.snd f) :=
    (reducedSingularHomologyι C R n).naturality
      (TopPair.Hom.snd f)
  apply (cancel_mono ((reducedSingularHomologyι C R n).app Q.snd)).mp
  have hLeft :
      ((relativeSingularHomologyFunctor C R (n + 1)).map f ≫
            (relativeSingularHomologyReducedIsoOfContractibleAmbient
              C R Q n).hom) ≫
          (reducedSingularHomologyι C R n).app Q.snd =
        (relativeSingularBoundary C R n).app P ≫
          ((singularHomologyFunctor C n).obj R).map
            (TopPair.Hom.snd f) := by
    rw [Category.assoc,
      relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_ι]
    exact hBoundary
  have hRight :
      ((relativeSingularHomologyReducedIsoOfContractibleAmbient
            C R P n).hom ≫
          (reducedSingularHomologyFunctor C R n).map
            (TopPair.Hom.snd f)) ≫
          (reducedSingularHomologyι C R n).app Q.snd =
        (relativeSingularBoundary C R n).app P ≫
          ((singularHomologyFunctor C n).obj R).map
            (TopPair.Hom.snd f) := by
    rw [Category.assoc, hReduced, ← Category.assoc,
      relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_ι]
    rfl
  exact hLeft.trans hRight.symm

end AlgebraicTopology
