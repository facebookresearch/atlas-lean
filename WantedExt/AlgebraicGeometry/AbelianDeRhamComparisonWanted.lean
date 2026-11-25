/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Perfectoid.BDeRham
public import Mathlib.RingTheory.WittVector.Compare
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-!
# de Rham comparison for the first cohomology of an abelian variety over a p-adic field

For a finite extension `F` of `ℚ_p` inside `\bar{ℚ}_p` and an abelian variety `A/F` of dimension
`g`, the `Gal(\bar{ℚ}_p/F)`-representation `V = H¹_ét(A_{\bar{ℚ}_p}, ℚ_p)` is de Rham, the jumps of
the Hodge filtration on `D_dR(V)` lie in `{0, 1}`, and `dim_F Fil¹ D_dR(V) = g`.

The period ring is Mathlib's `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`, the `(ker θ)`-adic completion of
`W(𝓞_ℂ_p^♭)[1/p]`, with `Fil^j B_dR^+` the kernel of the projection to
`W(𝓞_ℂ_p^♭)[1/p] ⧸ (ker θ)^j`. The Galois group acts on `𝓞_ℂ_p` by the completed action on
`ℂ_p`, on the tilt and on Witt vectors by functoriality, and on `B_dR^+` by continuity; the last
step uses that the action on `W(𝓞_ℂ_p^♭)[1/p]` preserves `ker θ`, recorded as a wanted theorem
together with the `p`-adic completeness of `𝓞_ℂ_p`. The `ℚ_p`-structure of `B_dR^+` comes from
`ℤ_p = W(𝔽_p) → W(𝓞_ℂ_p^♭)`. The groups `Fil^j D_dR(V) = (Fil^j B_dR^+ ⊗ V)^{G_F}`, `j ≥ 0`, are
then explicit, and de Rham with jumps in `{0, 1}` is a statement about their dimensions.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1
(2013), e1, Corollary 1.8, pp. 5–6, with Theorems 9.1 and 9.3, pp. 74–75.
https://doi.org/10.1017/fmp.2013.1
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AbelianDeRhamComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

theorem norm_completionGalois (σ : Galois p) (x : PadicComplex p) :
    ‖completionGalois p σ x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_completionGalois p σ).norm continuous_norm
  | ih a =>
    have h := completionGalois_coe p σ a
    change completionGalois p σ (a : PadicComplex p) = ((σ a : PadicAlgCl p) : PadicComplex p)
      at h
    rw [h, PadicComplex.norm_extends, PadicComplex.norm_extends, closure_norm_apply]

theorem mem_padicComplexInt_iff (x : PadicComplex p) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  let := Valued.toNormedField (PadicComplex p) NNReal
  exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm

instance padicComplexInt_fact_not_isUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := by
  refine ⟨fun h => ?_⟩
  have h1 := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.mp h
  rw [map_natCast, PadicComplex.valuation_p] at h1
  have h2 := h1.symm
  have hp : (1 : NNReal) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [eq_div_iff (by positivity), one_mul] at h2
  exact hp.ne' h2

/- The Galois action on `𝓞_ℂ_p`. -/
def integralGalois (σ : Galois p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  ((completionGalois p σ).toRingHom.comp (𝓞_ℂ_[p]).subtype).codRestrict (𝓞_ℂ_[p]) fun x => by
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [mem_padicComplexInt_iff]
    change ‖completionGalois p σ (x : PadicComplex p)‖ ≤ 1
    rw [norm_completionGalois, ← mem_padicComplexInt_iff]
    exact x.2

/- The Galois action on the tilt. -/
def tiltGalois (σ : Galois p) : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p :=
  Perfection.map p (Ideal.quotientMap (Ideal.span {(p : 𝓞_ℂ_[p])}) (integralGalois p σ) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span rfl))

abbrev Ainf := WittVector p (PreTilt 𝓞_ℂ_[p] p)

abbrev PreDeRham := Localization.Away (p : Ainf p)

/- The Galois action on `W(𝓞♭)[1/p]`. -/
def preDeRhamGalois (σ : Galois p) : PreDeRham p →+* PreDeRham p :=
  Localization.awayLift
    ((algebraMap (Ainf p) (PreDeRham p)).comp (WittVector.map (tiltGalois p σ))) (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p))

theorem preDeRhamGalois_comp_algebraMap (σ : Galois p) :
    (preDeRhamGalois p σ).comp (algebraMap (Ainf p) (PreDeRham p)) =
      (algebraMap (Ainf p) (PreDeRham p)).comp (WittVector.map (tiltGalois p σ)) :=
  IsLocalization.Away.lift_comp (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p))

/- The ring map `ℤ_p = W(𝔽_p) → W(𝓞♭)`. -/
def padicIntToAinf : ℤ_[p] →+* Ainf p :=
  (WittVector.map (ZMod.castHom dvd_rfl (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/- The ring map `ℚ_p → W(𝓞♭)[1/p]`. -/
def padicToPreDeRham : ℚ_[p] →+* PreDeRham p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (algebraMap (Ainf p) (PreDeRham p)).comp (padicIntToAinf p)) fun x => by
      obtain ⟨x, hx⟩ := x
      have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
      change IsUnit (((algebraMap (Ainf p) (PreDeRham p)).comp (padicIntToAinf p)) x)
      rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast]
      refine ((PadicInt.unitCoeff hx0).isUnit.map _).mul (IsUnit.pow _ ?_)
      simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p)

theorem preDeRhamGalois_comp_padicToPreDeRham (σ : Galois p) :
    (preDeRhamGalois p σ).comp (padicToPreDeRham p) = padicToPreDeRham p := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) ?_
  rw [RingHom.comp_assoc, padicToPreDeRham, IsLocalization.lift_comp, ← RingHom.comp_assoc,
    preDeRhamGalois_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  ext x n
  simp only [padicIntToAinf, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt 𝓞_ℂ_[p] p => f _)
    (RingHom.ext_zmod ((tiltGalois p σ).comp (ZMod.castHom dvd_rfl _)) (ZMod.castHom dvd_rfl _))

theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ?_
  have h := SModEq.sub_mem.mp (a.prop hle)
  rw [smul_eq_mul, Ideal.mul_top] at h
  simpa using (I ^ m).neg_mem h

/- The ring of integers `𝓞_ℂ_p = {x : ‖x‖ ≤ 1}` of `ℂ_p` is `p`-adically separated and complete,
since `p ^ n 𝓞_ℂ_p = {x : ‖x‖ ≤ p ^ (-n)}` and `ℂ_p` is complete. This is the case `C = ℂ_p` of
`WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization.integers_adic_complete`, stated for
Mathlib's `𝓞_ℂ_[p]`, whose `p`-adic completeness `BDeRhamPlus` takes as an instance. -/
public instance_wanted padicComplexInt_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]

section Completion

variable [IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]]

/- The kernel of `θ : W(𝓞♭)[1/p] → ℂ_p`. -/
abbrev thetaKer : Ideal (PreDeRham p) := RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/- `B_dR^+`, with its `ℚ_p`-algebra structure. -/
def BdRPlus : Type := BDeRhamPlus 𝓞_ℂ_[p] p

instance : CommRing (BdRPlus p) := inferInstanceAs (CommRing (BDeRhamPlus 𝓞_ℂ_[p] p))

/- The canonical map `W(𝓞♭)[1/p] → B_dR^+`. -/
def ofPreDeRham : PreDeRham p →+* BdRPlus p :=
  algebraMap (PreDeRham p) (AdicCompletion (thetaKer p) (PreDeRham p))

instance : Algebra ℚ_[p] (BdRPlus p) := ((ofPreDeRham p).comp (padicToPreDeRham p)).toAlgebra

/- The projection `B_dR^+ → W(𝓞♭)[1/p] ⧸ (ker θ)^n`. -/
def evalBdR (n : ℕ) : BdRPlus p →+* PreDeRham p ⧸ thetaKer p ^ n :=
  (AdicCompletion.evalₐ (thetaKer p) n).toRingHom

/- `Fil^j B_dR^+`. -/
def fil (j : ℕ) : Ideal (BdRPlus p) := RingHom.ker (evalBdR p j)

theorem pow_le_comap {f : PreDeRham p →+* PreDeRham p} (h : thetaKer p ≤ (thetaKer p).comap f)
    (n : ℕ) : thetaKer p ^ n ≤ (thetaKer p ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n

/- The Galois action on `B_dR^+`. -/
def bdRPlusGalois (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) :
    BdRPlus p →+* BdRPlus p :=
  AdicCompletion.liftRingHom (thetaKer p)
    (fun n => (Ideal.quotientMap (thetaKer p ^ n) (preDeRhamGalois p σ)
      (pow_le_comap p h n)).comp (evalBdR p n))
    (fun {m n} hle => by
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalBdR p n x)
      have hm : evalBdR p m x = Ideal.Quotient.mk _ y := by
        change AdicCompletion.evalₐ (thetaKer p) m x = _
        rw [← factorPow_evalₐ (thetaKer p) hle x]
        change Ideal.Quotient.factorPow _ hle (evalBdR p n x) = _
        rw [← hy]
        simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      simp only [RingHom.coe_comp, Function.comp_apply, hm, ← hy, Ideal.quotientMap_mk,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])

theorem bdRPlusGalois_ofPreDeRham (σ : Galois p)
    (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) (x : PreDeRham p) :
    bdRPlusGalois p σ h (ofPreDeRham p x) = ofPreDeRham p (preDeRhamGalois p σ x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  change AdicCompletion.evalₐ _ n (AdicCompletion.liftRingHom _ _ _ _) = _
  rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply]
  change Ideal.quotientMap _ _ (pow_le_comap p h n)
      (AdicCompletion.evalₐ (thetaKer p) n (AdicCompletion.of (thetaKer p) (PreDeRham p) x)) =
    AdicCompletion.evalₐ (thetaKer p) n
      (AdicCompletion.of (thetaKer p) (PreDeRham p) (preDeRhamGalois p σ x))
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

/- The Galois action on `B_dR^+`, as a `ℚ_p`-linear map. -/
def bdRPlusGaloisLinear (σ : Galois p)
    (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) :
    BdRPlus p →ₗ[ℚ_[p]] BdRPlus p where
  toFun := bdRPlusGalois p σ h
  map_add' := map_add _
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    change bdRPlusGalois p σ h (ofPreDeRham p (padicToPreDeRham p c)) =
      ofPreDeRham p (padicToPreDeRham p c)
    rw [bdRPlusGalois_ofPreDeRham, ← RingHom.comp_apply (preDeRhamGalois p σ),
      preDeRhamGalois_comp_padicToPreDeRham]

end Completion

set_option linter.concreteInstances false in
/-- **Galois equivariance of Fontaine's $\theta$.** Let
$\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ act on
$\mathcal{O}_{\mathbb{C}_p}$ through its continuous extension to $\mathbb{C}_p$, on
$\mathcal{O}_{\mathbb{C}_p}^\flat =
\varprojlim_{x \mapsto x^p} \mathcal{O}_{\mathbb{C}_p}/p$ coordinatewise, and on
$W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$ by functoriality of Witt vectors and localization. Then
$\sigma$ maps the kernel of Fontaine's map
$\theta \colon W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p] \to \mathcal{O}_{\mathbb{C}_p}[1/p]$ into
itself, so it extends by continuity to the $(\ker\theta)$-adic completion $B_{\mathrm{dR}}^+$.

J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of
2022-05-26), Lemma 6.9, p. 139 ($\theta$ commutes with the Galois action) and §6.2.2, p. 140 (its
extension to $W(R)[1/p]$ is equivariant), archived at
<http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>. -/
public theorem_wanted thetaKer_le_comap_preDeRhamGalois (σ : Galois p) :
    thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)

section Cohomology

variable [IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]]
variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (A : Over (Spec (CommRingCat.of F)))

/- `H¹_ét(A_{\bar F}, ℚ_p)`. -/
abbrev H1 : Type 1 := AdicCohomology p (geometricFibre A (PadicAlgCl p)) 1

/- The action of `Gal(\bar F / F)` on `H¹_ét(A_{\bar F}, ℚ_p)`. -/
def h1Galois (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) : H1 p F A →ₗ[ℚ_[p]] H1 p F A :=
  continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
    (galoisSchemeOperator A (PadicAlgCl p) σ) 1

/- `Fil^j D_dR` for `j ≥ 0`. -/
def filDeRham (h : ∀ τ : Galois p, thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p τ))
    (j : ℕ) : Submodule ℚ_[p] (BdRPlus p ⊗[ℚ_[p]] H1 p F A) :=
  LinearMap.range (TensorProduct.map ((fil p j).restrictScalars ℚ_[p]).subtype
      (LinearMap.id : H1 p F A →ₗ[ℚ_[p]] H1 p F A)) ⊓
    ⨅ σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p,
      LinearMap.eqLocus
        (TensorProduct.map (bdRPlusGaloisLinear p (σ.restrictScalars ℚ_[p]) (h _))
          (h1Galois p F A σ)) LinearMap.id

end Cohomology

set_option linter.concreteInstances false in
/-- **de Rham comparison for $H^1$ of an abelian variety.** Let $F$ be a finite extension of
$\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$ and let $A/F$ be an abelian variety of dimension
$g$: a commutative group object over $\operatorname{Spec} F$ that is proper, geometrically
connected and smooth of relative dimension $g$. Let
$V = H^1_{\mathrm{et}}(A_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p)$, on which
$\sigma \in G_F = \operatorname{Gal}(\overline{\mathbb{Q}}_p/F)$ acts by inverse image along
$\mathrm{id}_A \times \operatorname{Spec} \sigma$. Then $V$ is finite-dimensional and de Rham, the
jumps of the Hodge filtration on $D_{\mathrm{dR}}(V)$ lie in $\{0, 1\}$, and
$\dim_F \operatorname{Fil}^1 D_{\mathrm{dR}}(V) = g$.

Here $B_{\mathrm{dR}}^+$ is the $(\ker\theta)$-adic completion of
$W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$, $\operatorname{Fil}^j B_{\mathrm{dR}}^+$ is the kernel
of its projection to $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]/(\ker\theta)^j$ (that is,
$t^j B_{\mathrm{dR}}^+$), and
$D^j = (\operatorname{Fil}^j B_{\mathrm{dR}}^+ \otimes_{\mathbb{Q}_p} V)^{G_F}$ for $j \ge 0$.
The conclusion reads: $V$ is finite-dimensional,
$\dim_{\mathbb{Q}_p} D^0 = [F : \mathbb{Q}_p] \dim_{\mathbb{Q}_p} V$,
$\dim_{\mathbb{Q}_p} D^1 = [F : \mathbb{Q}_p]\, g$, and $D^2 = 0$. Since
$D_{\mathrm{dR}}(V) = (B_{\mathrm{dR}} \otimes_{\mathbb{Q}_p} V)^{G_F}$ is an $F$-vector space of
dimension at most $\dim_{\mathbb{Q}_p} V$ and $D^j = \operatorname{Fil}^j D_{\mathrm{dR}}(V)$, the
first equality says that $V$ is de Rham with
$\operatorname{Fil}^0 D_{\mathrm{dR}}(V) = D_{\mathrm{dR}}(V)$, and the others say
$\dim_F \operatorname{Fil}^1 D_{\mathrm{dR}}(V) = g$ and
$\operatorname{Fil}^2 D_{\mathrm{dR}}(V) = 0$. Taking as Hodge–Tate weights the jumps $j$, counted
with multiplicity $\dim_F \operatorname{gr}^j D_{\mathrm{dR}}(V)$ (the convention in which
$\mathbb{Q}_p(1)$ has weight $-1$), $V$ has weights in $\{0, 1\}$, the weight $1$ with
multiplicity $g$. Étale cohomology with $\mathbb{Q}_p$ coefficients is the pro-étale cohomology of
the sheaf of continuous $\mathbb{Q}_p$-valued functions. The Galois action on
$B_{\mathrm{dR}}^+$ extends that on $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$, which preserves
$\ker\theta$.

Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), e1,
[Corollary 1.8, pp. 5–6](https://doi.org/10.1017/fmp.2013.1): for a proper smooth rigid-analytic
variety $X$ over $F$, $H^i(X_{\bar F, \mathrm{et}}, \mathbb{Q}_p)$ is de Rham with associated
filtered $F$-vector space $H^i_{\mathrm{dR}}(X)$. It applies to the analytification of $A$ by
Theorems 9.1 and 9.3, pp. 74–75 (coherent and étale cohomology of a proper scheme and of its
analytification agree); the corrigendum, Forum Math. Pi 4 (2016), e6,
<https://doi.org/10.1017/fmp.2016.4>, keeps these results. For $i = 1$ the Hodge filtration of
$H^1_{\mathrm{dR}}(A/F)$ has $\operatorname{Fil}^0 = H^1_{\mathrm{dR}}(A/F)$,
$\operatorname{Fil}^1 = H^0(A, \Omega^1_A)$, of dimension $g$, and $\operatorname{Fil}^2 = 0$. -/
public theorem_wanted abelianVariety_h1_deRham
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (A : Over (Spec (CommRingCat.of F))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [GeometricallyConnected A.hom] (g : ℕ) [SmoothOfRelativeDimension g A.hom] :
    FiniteDimensional ℚ_[p] (H1 p F A) ∧
      Module.finrank ℚ_[p] (filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 0) =
        Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] (H1 p F A) ∧
      Module.finrank ℚ_[p] (filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 1) =
        Module.finrank ℚ_[p] F * g ∧
      filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 2 = ⊥

end WantedExt.AlgebraicGeometry.AbelianDeRhamComparison
