/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ResidueField.DVR
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Smooth.Flat

/-!
# DVR residue-field fullness: source-map stage for ATLAS N211

This module is Stage C for ATLAS NumberTheoryI item N211, Theorem 10.13
(Section 10.2), at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`. See the immutable
[N211 / Theorem 10.13 target, lines 1465-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1465-L1483).
The source implementation is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean).

Source map from ATLAS N211 / Theorem 10.13 to this module's API:

* The imported Stage A module `MathlibExt.RingTheory.LocalRing.ResidueField.DVR`
  supplies locality and `DVRResidue.residueFieldMapAlgHom`.
* `DVRResidue.exists_root_lift_of_adjoin_eq_top` is the Henselian
  root-lifting step: `A` and `B` are local DVRs with a finite `A`-module
  structure on `B`, `Algebra.Etale A B` supplies the formal-unramified /
  separable source condition, `C` is a Henselian local target, and a monogenic
  generator of `B` lifts the target residue class to a root of the generator's
  minimal polynomial in `C`; the helper omits `IsDomain C`,
  `IsDiscreteValuationRing C`, and `Module.Finite A C`, so it does not require
  `C` to be a DVR; cf. the surjectivity half of
  [`residueFieldFunctor_full_faithfulness`, lines 1110-1165](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1110-L1165),
  which constructs an
  algebra homomorphism lifting a residue-field homomorphism using a monogenic
  presentation and Hensel lifting.
* `DVRResidue.residueFieldMapAlgHom_surjective` formalizes the
  fullness/surjectivity direction of the Hom-set bijection in Theorem 10.13 by
  turning that lifted root into an `A`-algebra homomorphism whose residue map is
  the requested homomorphism; cf. `residueFieldFunctorAlg`, lines 1001-1011,
  which defines the induced residue-field map
  ([immutable source](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1001-L1011)).
* Stage B's `DVRResidue.residueFieldMapAlgHom_injective` is the separate
  faithfulness half; this module need not import or restate it, but the two
  later combine into Hom-set bijectivity.

This is not the full N211 target: essential surjectivity on finite separable
residue extensions, compatible lifting of residue-field equivalences, and the
category-equivalence/isomorphism-class conclusion remain later stages; cf.
[`residueFieldFunctor_isEquivalence`, lines 1320-1338](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338),
which packages full
faithfulness, essential surjectivity, and compatible lifting of residue-field
equivalences. Recovering the source theorem's complete-DVR / unramified
presentation from these generalized hypotheses is handled by later N211 bridge
stages; this module alone does not prove that bridge.
-/

@[expose] public section

variable {A B C : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Finite A B] [Module.Finite A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [Algebra.Etale A B] [HenselianLocalRing C]

namespace DVRResidue

omit [IsDomain C] [IsDiscreteValuationRing C] [Module.Finite A C] in
/-- **Lifting residue-field images to roots of a minimal polynomial.** Let $A$ and $B$ be
discrete valuation rings with $B$ a finite étale $A$-algebra whose structure map is local, and
let $C$ be a Henselian local ring that is an $A$-algebra whose structure map is local. Write
$k_A$, $k_B$, $k_C$ for the residue fields. Let $\beta \in B$ generate $B$ as an $A$-algebra,
and let $\bar\beta \in k_B$ be its residue class. Then for every $k_A$-algebra homomorphism
$f : k_B \to k_C$ there is $\gamma \in C$ that is a root of the minimal polynomial of $\beta$
over $A$ and whose residue class in $k_C$ is $f(\bar\beta)$. -/
theorem exists_root_lift_of_adjoin_eq_top
    {beta : B} (hbeta : Algebra.adjoin A {beta} = ⊤)
    (f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    exists gamma : C, Polynomial.aeval gamma (minpoly A beta) = 0 /\
      IsLocalRing.residue C gamma = f (IsLocalRing.residue B beta) := by
  have hInt : IsIntegral A beta := Algebra.IsIntegral.isIntegral beta
  let q : Polynomial A := minpoly A beta
  let P : Polynomial C := q.map (algebraMap A C)
  let rB : IsLocalRing.ResidueField B := IsLocalRing.residue B beta
  let a0 : IsLocalRing.ResidueField C := f rB
  let : Module.Free A B := Module.free_of_flat_of_isLocalRing
  have hPmonic : P.Monic := (minpoly.monic hInt).map _
  have h2 := ((HenselianLocalRing.TFAE C).out 1 2).mp
    (inferInstance : HenselianLocalRing C)
  have hcomp : (IsLocalRing.residue C).comp (algebraMap A C) =
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)).comp
        (IsLocalRing.residue A) := by
    rw [show algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) =
      IsLocalRing.ResidueField.map (algebraMap A C) from rfl]
    exact (IsLocalRing.ResidueField.map_comp_residue (algebraMap A C)).symm
  have hred : P.map (IsLocalRing.residue C) =
      (minpoly (IsLocalRing.ResidueField A) rB).map
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)) := by
    simp only [P, q, Polynomial.map_map]
    rw [hcomp, ← Polynomial.map_map, IsLocalRing.minpoly_map_residue hbeta]
  have hmin : Polynomial.aeval rB (minpoly (IsLocalRing.ResidueField A) rB) = 0 :=
    minpoly.aeval _ _
  have hrootB : ((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B))).IsRoot rB := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
    exact hmin
  have hbase : f.toRingHom.comp
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) =
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) := by
    ext r
    exact f.commutes r
  have hmapEq : (((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).map
      f.toRingHom) =
      (minpoly (IsLocalRing.ResidueField A) rB).map
        (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField C)) := by
    rw [Polynomial.map_map, hbase]
  have hrootC' : ((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField C))).IsRoot a0 := by
    have h := hrootB.map (f := f.toRingHom)
    rw [hmapEq] at h
    change ((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField C))).IsRoot (f.toRingHom rB)
    exact h
  have hP : (P.map (IsLocalRing.residue C)).IsRoot a0 := by
    rw [hred]
    exact hrootC'
  have hroot0 : Polynomial.aeval a0 P = 0 := by
    have hPeval : (P.map (IsLocalRing.residue C)).eval a0 = 0 :=
      Polynomial.IsRoot.def.mp hP
    rw [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← Polynomial.eval_map]
    exact hPeval
  have hsep : (minpoly (IsLocalRing.ResidueField A) rB).Separable :=
    Algebra.IsSeparable.isSeparable _ _
  have hsepC : ((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField C))).Separable := by
    exact hsep.map
  have hsepP : (P.map (IsLocalRing.residue C)).Separable := by
    rw [hred]
    exact hsepC
  have hP_aeval : Polynomial.aeval a0 (P.map (IsLocalRing.residue C)) = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.IsRoot.def] using hP
  have hne := hsepP.aeval_derivative_ne_zero hP_aeval
  have hderiv0 : Polynomial.aeval a0 P.derivative ≠ 0 := by
    simpa [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
      Polynomial.derivative_map, Polynomial.eval_map] using hne
  obtain ⟨gamma, hroot, hres⟩ := h2 P hPmonic a0 hroot0 hderiv0
  refine ⟨gamma, ?_, hres⟩
  simpa [P, Polynomial.IsRoot.def] using hroot

/-- **Lifting residue-field homomorphisms of finite étale DVR extensions.** Let $A$, $B$, $C$ be
discrete valuation rings, with $B$ and $C$ finite $A$-algebras whose structure maps are local,
$B$ étale over $A$ and $C$ Henselian. Write $k_A$, $k_B$, $k_C$ for the residue fields. Then
every $k_A$-algebra homomorphism $k_B \to k_C$ is induced by an $A$-algebra homomorphism: the
map sending an $A$-algebra homomorphism $\varphi : B \to C$ to the induced homomorphism of
residue fields $k_B \to k_C$, $\bar b \mapsto \overline{\varphi(b)}$, is surjective. -/
theorem residueFieldMapAlgHom_surjective :
    Function.Surjective
      (residueFieldMapAlgHom (A := A) (B := B) (C := C)) := by
  classical
  let : Module.Free A B := Module.free_of_flat_of_isLocalRing
  obtain ⟨beta, hbeta⟩ := IsLocalRing.exists_adjoin_eq_top (R := A) (S := B)
  intro f
  obtain ⟨gamma, hgamma, hres⟩ :=
    exists_root_lift_of_adjoin_eq_top hbeta f
  let hRoot := IsAdjoinRootMonic.mkOfAdjoinEqTop' hbeta
  let phi : B →ₐ[A] C := hRoot.liftHom gamma hgamma
  refine ⟨phi, ?_⟩
  refine AlgHom.ext_of_adjoin_eq_top
    ((IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top beta).mpr hbeta) ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  change residueFieldMapAlgHom phi (IsLocalRing.residue B beta) = _
  rw [residueFieldMapAlgHom_residue]
  change IsLocalRing.residue C (hRoot.liftHom gamma hgamma beta) = _
  have hbetaRoot : hRoot.root = beta := by
    dsimp only [hRoot]
    exact IsAdjoinRootMonic.mkOfAdjoinEqTop'_root hbeta
  have hphiBeta : hRoot.liftHom gamma hgamma beta = gamma := by
    simpa only [hbetaRoot] using hRoot.liftHom_root hgamma
  rw [hphiBeta]
  exact hres

end DVRResidue
