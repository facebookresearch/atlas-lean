/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionMonad
public import MathlibExt.CategoryTheory.Monad.Coresolution
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Continuous coinduction coresolutions and homogeneous resolutions

Let G be a compact, totally disconnected topological group in universe u. Discrete continuous
abelian coefficients lie in W=max(u,w), and J sends these actions to continuous
ℤ-representations. The diagonal coinduction monad T has constant-function unit and
multiplication F↦(g↦F(g)(g)).

The comparison J(T^n A)≅C^n(JA) identifies the monad coresolution in degree n with the shifted
homogeneous resolution term C^{n+1}(JA). In outer-to-inner function-coordinate order, cofaces
omit a coordinate and codegeneracies repeat adjacent coordinates. The cochain differential in
degree n is the sum of the n+2 cofaces with signs (-1)^i. The degree comparisons give an
isomorphism of the full nonnegative cochain complexes and send the coaugmentation to the
constant-function inclusion.

For continuous representations, the coface formulas require only a topological group. The
diagonal and codegeneracies require compactness, independently of total disconnectedness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w v₀ u₀
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). For a coefficient action A, the
comparison j_A:J(TA)≅C(JA) identifies the two continuous function spaces C(G,JA). Its forward
and inverse maps leave every function value unchanged, and both carry the action
(h•F)(g)=h•F(h⁻¹g). -/
def coindToTopRepIso (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.obj (coind.{u, w}.obj A) ≅ (toTopRep.obj A).coind₁ :=
  TopRep.toActionFromAction ((toTopRep.obj A).coind₁)

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Let j_A:J(TA)≅C(JA) compare
discrete-action coinduction with representation coinduction. For every continuous coinduced
function F:G→A and g∈G, (j_A.hom F)(g)=F(g). -/
theorem coindToTopRepIso_hom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (z : underlying (coind.{u, w}.obj A)) (g : G) :
    ((coindToTopRepIso.{u, w} G A).hom.hom z) g = coindFunction.{u, w} A z g := rfl

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Let j_A:J(TA)≅C(JA) compare
discrete-action coinduction with representation coinduction. For F∈C(JA) and g∈G, the inverse
comparison satisfies (j_A.inv F)(g)=F(g). -/
theorem coindToTopRepIso_inv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (z : (toTopRep.obj A).coind₁) (g : G) :
    coindFunction.{u, w} A ((coindToTopRepIso.{u, w} G A).inv.hom z) g = z g := rfl

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For an equivariant additive coefficient morphism f:A→B, the
isomorphisms j_A:J(TA)≅C(JA) satisfy J(Tf)≫j_B.hom=j_A.hom≫C(Jf). Both paths apply f pointwise
to the same continuous functions. -/
theorem coindToTopRepIso_naturality {A B : DiscreteAbelianAction.{u, max u w} G}
    (f : A ⟶ B) :
    toTopRep.map (coind.{u, w}.map f) ≫ (coindToTopRepIso.{u, w} G B).hom =
      (coindToTopRepIso.{u, w} G A).hom ≫ (TopRep.coind₁Functor ℤ G).map (toTopRep.map f) := by
  rfl

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For every A, let η_A:A→TA be the monad unit and ι_{JA}:JA→C(JA)
the constant-function inclusion. Then J(η_A)≫j_A.hom=ι_{JA}, where j_A:J(TA)≅C(JA). -/
theorem coindToTopRepIso_unit (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((coindMonad.{u, w} G).η.app A) ≫ (coindToTopRepIso.{u, w} G A).hom =
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (toTopRep.obj A) := by
  have h := congrArg (fun f : A ⟶ coind.{u, w}.obj A =>
    toTopRep.map f ≫ (coindToTopRepIso.{u, w} G A).hom) (coindMonad_unit.{u, w} G A)
  exact h.trans (by rfl)

/-- Let G be a topological group in universe u and X a continuous ℤ-representation with coefficient
universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0 and 0≤i≤n,
c_i^n:R_n(X)→R_{n+1}(X) inserts a constant function coordinate. The outer coface c_0^n is the
constant inclusion of R_n(X), and c_{i+1}^{n+1}=C(c_i^n). Thus, in nested-function coordinates,
c_i^n ignores the newly inserted i-th coordinate. -/
def coindResolutionCoface (X : TopRep.{max u w, 0, u} ℤ G) :
    (n : ℕ) → Fin (n + 1) → (TopRep.resolutionX X n ⟶ TopRep.resolutionX X (n + 1))
  | 0, _ => (TopRep.coind₁ι (k := ℤ) (G := G)).app X
  | n + 1, ⟨0, _⟩ =>
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX X (n + 1))
  | n + 1, ⟨i + 1, hi⟩ =>
      (TopRep.coind₁Functor ℤ G).map
        (coindResolutionCoface X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Let G be a topological group in universe u and X a continuous ℤ-representation with coefficient
universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For every n≥0,
c_0^n:R_n(X)→R_{n+1}(X) is the constant-function inclusion ι_{R_n(X)}. It sends a nested
function F to the function g↦F, so the new outer G-coordinate does not change its value. -/
theorem coindResolutionCoface_zero (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    coindResolutionCoface.{u, w} G X n 0 =
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX X n) := by
  cases n <;> rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Let G be a topological group in universe u and X a continuous ℤ-representation with coefficient
universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0 and
i∈{0,…,n}, the nested-resolution cofaces obey c_{i+1}^{n+1}=C(c_i^n). Here
c_i^n:R_n(X)→R_{n+1}(X), and applying C gives a morphism R_{n+1}(X)→R_{n+2}(X) that inserts the
coordinate one position farther inward. -/
theorem coindResolutionCoface_succ (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ)
    (i : Fin (n + 1)) :
    coindResolutionCoface.{u, w} G X (n + 1) i.succ =
      (TopRep.coind₁Functor ℤ G).map (coindResolutionCoface.{u, w} G X n i) := rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a topological group in universe u and X a continuous ℤ-representation with coefficient
universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0, the
homogeneous resolution differential d_X(n):R_n(X)→R_{n+1}(X) is Σ_{i=0}^n (-1)^i c_i^n. The sign
uses the outer-to-inner coface index i; in particular d_X(0) is the constant inclusion, and
d_X(n+1)=ι_{R_{n+1}(X)}-C(d_X(n)). -/
theorem coindResolutionCoface_sum (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • coindResolutionCoface.{u, w} G X n i) =
      TopRep.d X n := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, pow_zero, one_zsmul, coindResolutionCoface, TopRep.d_zero]
      rfl
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_zsmul,
        coindResolutionCoface_zero, coindResolutionCoface_succ]
      rw [TopRep.d_succ, ← ih, Functor.map_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
      exact congrArg (fun f => -f)
        (Functor.map_smul (TopRep.coind₁Functor ℤ G) ((-1 : ℤ) ^ i.val)
          (coindResolutionCoface.{u, w} G X n i)).symm

private theorem barEtaZeroInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (A : C) :
    Monad.barEtaAtPos T n 0 A ≫ eqToHom (Monad.monadPow_succ_obj_eq T n A) =
      T.η.app ((Monad.monadPow T n).obj A) := by
  simp only [Monad.barEtaAtPos, Fin.rev_zero]
  induction n generalizing A with
  | zero => exact Category.comp_id _
  | succ n ih => exact ih (T.obj A)

private theorem etaCastSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.etaAtPos T (n + 1) i.castSucc A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T n A) ≫ T.map (Monad.etaAtPos T n i A) := by
  induction n generalizing A with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact Monad.monadPow_obj_T_comm_naturality T 0 (T.η.app A)
  | succ n ih =>
      cases i with
      | mk val hval =>
          cases val with
          | zero =>
              exact Monad.monadPow_obj_T_comm_naturality T (n + 1) (T.η.app A)
          | succ k =>
              exact ih ⟨k, Nat.lt_of_succ_lt_succ hval⟩ (T.obj A)

private theorem barEtaSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.barEtaAtPos T (n + 1) i.succ A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T n A) ≫ T.map (Monad.barEtaAtPos T n i A) := by
  simp only [Monad.barEtaAtPos, Fin.rev_succ]
  exact etaCastSuccInPowers T n i.rev A

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For A and n≥0, E_A^n:J(T^n A)≅R_n(JA) identifies n-fold monad
coinduction with n nested representation coinductions. The degree-zero comparison is the
identity, and E_A^{n+1} is the canonical reassociation J(T^{n+1}A)≅J(T(T^n A)), followed by
j_{T^n A} and C(E_A^n). -/
def coindPowerToTopRepIso (A : DiscreteAbelianAction.{u, max u w} G) :
    (n : ℕ) → toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≅
      TopRep.resolutionX (toTopRep.obj A) n
  | 0 => Iso.refl (toTopRep.obj A)
  | n + 1 =>
      toTopRep.mapIso (eqToIso (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≪≫
      coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≪≫
      (TopRep.coind₁Functor ℤ G).mapIso (coindPowerToTopRepIso A n)

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let K_A be the cosimplicial monad coresolution, with
κ_A^n:K_A^n≅T^{n+1}A. In degree n≥0, the comparison e_A^n:J(K_A^n)≅R_{n+1}(JA) is J(κ_A^n)
followed by E_A^{n+1}. Its target is degree n of the shifted homogeneous resolution. -/
def coindCoresolutionTermIso (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.obj ((Monad.coresolution (coindMonad.{u, w} G) A).obj (SimplexCategory.mk n)) ≅
      TopRep.resolution'X (toTopRep.obj A) n :=
  toTopRep.mapIso (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n) ≪≫
    coindPowerToTopRepIso.{u, w} G A (n + 1)

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let α_A^n:T^{n+1}A≅T(T^n A) be the canonical reassociation of
powers and j_B:J(TB)≅C(JB). For n≥0, the forward comparison satisfies
(E_A^{n+1}).hom=J((α_A^n).hom)≫j_{T^n A}.hom≫C((E_A^n).hom). -/
theorem coindPowerToTopRepIso_succ_hom (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
      (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom ≫
      (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := rfl

private theorem threeSquareComposite {C : Type u₀} [Category.{v₀} C]
    {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁) (d : D₀ ⟶ D₁)
    (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁)
    (f₀ : B₀ ⟶ C₀) (f₁ : B₁ ⟶ C₁)
    (g₀ : C₀ ⟶ D₀) (g₁ : C₁ ⟶ D₁)
    (ha : a ≫ e₁ = e₀ ≫ b) (hb : b ≫ f₁ = f₀ ≫ c) (hc : c ≫ g₁ = g₀ ≫ d) :
    a ≫ (e₁ ≫ f₁ ≫ g₁) = (e₀ ≫ f₀ ≫ g₀) ≫ d := by
  calc
    a ≫ (e₁ ≫ f₁ ≫ g₁) = (a ≫ e₁) ≫ f₁ ≫ g₁ := (Category.assoc _ _ _).symm
    _ = (e₀ ≫ b) ≫ f₁ ≫ g₁ := congrArg (fun f => f ≫ f₁ ≫ g₁) ha
    _ = e₀ ≫ (b ≫ f₁) ≫ g₁ := by simp only [Category.assoc]
    _ = e₀ ≫ (f₀ ≫ c) ≫ g₁ := congrArg (fun f => e₀ ≫ f ≫ g₁) hb
    _ = e₀ ≫ f₀ ≫ (c ≫ g₁) := by simp only [Category.assoc]
    _ = e₀ ≫ f₀ ≫ (g₀ ≫ d) := congrArg (fun f => e₀ ≫ f₀ ≫ f) hc
    _ = (e₀ ≫ f₀ ≫ g₀) ≫ d := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For n≥0, write u_0^n:T^n A→T^{n+1}A for the outer unit
insertion. The power comparisons satisfy J(u_0^n)≫(E_A^{n+1}).hom=(E_A^n).hom≫ι_{R_n(JA)}. Thus
the outer monad coface becomes the constant-coordinate inclusion. -/
theorem coindPowerToTopRepIso_coface_zero (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A n).hom ≫
        (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX (toTopRep.obj A) n) := by
  rw [coindPowerToTopRepIso_succ_hom]
  have hp := (Functor.map_comp toTopRep (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A)
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))).symm.trans
      (congrArg (fun f => toTopRep.map f) (barEtaZeroInPowers (coindMonad.{u, w} G) n A))
  have hu := coindToTopRepIso_unit.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
  calc
    _ = ((toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A) ≫
        toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))) ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := by
      simp only [Category.assoc]
    _ = (toTopRep.map ((coindMonad.{u, w} G).η.app
          ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
      congrArg (fun f => (f ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom) hp
    _ = (TopRep.coind₁ι (k := ℤ) (G := G)).app
          (toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
      congrArg (fun f => f ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom) hu
    _ = _ := ((TopRep.coind₁ι (k := ℤ) (G := G)).naturality
      (coindPowerToTopRepIso.{u, w} G A n).hom).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For n≥0 and 0≤i≤n, let u_i^n:T^n A→T^{n+1}A be the monad unit
insertion in coface position i. Then J(u_i^n)≫(E_A^{n+1}).hom=(E_A^n).hom≫c_i^n, with
c_i^n:R_n(JA)→R_{n+1}(JA) indexed from the outer function coordinate inward. -/
theorem coindPowerToTopRepIso_coface (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n i A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A n).hom ≫
        coindResolutionCoface.{u, w} G (toTopRep.obj A) n i := by
  induction n with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      simpa only [coindResolutionCoface_zero] using coindPowerToTopRepIso_coface_zero.{u, w} G A 0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [coindResolutionCoface_zero] using
          coindPowerToTopRepIso_coface_zero.{u, w} G A (n + 1)
      · let φ := Monad.barEtaAtPos (coindMonad.{u, w} G) n j A
        have hp := (Functor.map_comp toTopRep
          (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) j.succ A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))).symm.trans
            ((congrArg (fun f => toTopRep.map f)
              (barEtaSuccInPowers (coindMonad.{u, w} G) n j A)).trans
                (Functor.map_comp toTopRep
                  (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
                  ((coindMonad.{u, w} G).map φ)))
        have hj := coindToTopRepIso_naturality.{u, w} G φ
        have hh := (Functor.map_comp (TopRep.coind₁Functor ℤ G) (toTopRep.map φ)
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom).symm.trans
            ((congrArg (fun f => (TopRep.coind₁Functor ℤ G).map f) (ih j)).trans
              (Functor.map_comp (TopRep.coind₁Functor ℤ G)
                (coindPowerToTopRepIso.{u, w} G A n).hom
                (coindResolutionCoface.{u, w} G (toTopRep.obj A) n j)))
        rw [coindPowerToTopRepIso_succ_hom G A (n + 1),
          coindPowerToTopRepIso_succ_hom G A n, coindResolutionCoface_succ]
        exact threeSquareComposite
          (toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) j.succ A))
          (toTopRep.map ((coindMonad.{u, w} G).map φ))
          ((TopRep.coind₁Functor ℤ G).map (toTopRep.map φ))
          ((TopRep.coind₁Functor ℤ G).map (coindResolutionCoface.{u, w} G (toTopRep.obj A) n j))
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)))
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A)))
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)).hom
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom)
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom)
          hp hj hh

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For the monad coresolution K_A and κ_A^n:K_A^n≅T^{n+1}A, the
degree-n comparison e_A^n:J(K_A^n)≅R_{n+1}(JA) has forward map
(e_A^n).hom=J((κ_A^n).hom)≫(E_A^{n+1}).hom, for every n≥0. -/
theorem coindCoresolutionTermIso_hom (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    (coindCoresolutionTermIso.{u, w} G A n).hom =
      toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let e_A^n:J(K_A^n)≅R_{n+1}(JA) be the monad coresolution term
comparison. For n≥0 and 0≤i≤n+1, the cosimplicial coface δ_i:K_A^n→K_A^{n+1} satisfies
J(δ_i)≫(e_A^{n+1}).hom=(e_A^n).hom≫c_i^{n+1}. -/
theorem coindCoresolution_coface (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 2)) :
    toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i)) ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫
        coindResolutionCoface.{u, w} G (toTopRep.obj A) (n + 1) i := by
  rw [coindCoresolutionTermIso_hom, coindCoresolutionTermIso_hom]
  have hc := (Functor.map_comp toTopRep
    ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i))
    (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom).symm.trans
      ((congrArg (fun f => toTopRep.map f)
        (Monad.coresolutionObjIso_coface (coindMonad.{u, w} G) A i)).trans
          (Functor.map_comp toTopRep (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom
            (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A)))
  have hp := coindPowerToTopRepIso_coface.{u, w} G A (n + 1) i
  calc
    _ = (toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i)) ≫
        toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom := (Category.assoc _ _ _).symm
    _ = (toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A)) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom :=
      congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom) hc
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        (toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom) := Category.assoc _ _ _
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        ((coindPowerToTopRepIso.{u, w} G A (n + 1)).hom ≫
          coindResolutionCoface.{u, w} G (toTopRep.obj A) (n + 1) i) :=
      congrArg (fun f => toTopRep.map
        (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫ f) hp
    _ = _ := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For the cosimplicial monad coresolution K_A, put
D_n=Σ_{i=0}^{n+1}(-1)^i J(δ_i):J(K_A^n)→J(K_A^{n+1}). The term comparisons
e_A^n:J(K_A^n)≅R_{n+1}(JA) satisfy D_n≫(e_A^{n+1}).hom=(e_A^n).hom≫d_{JA}(n+1). No additional
degree sign enters this comparison. -/
theorem coindCoresolution_differential (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) n ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫ TopRep.d (toTopRep.obj A) (n + 1) := by
  rw [← coindResolutionCoface_sum.{u, w} G (toTopRep.obj A) (n + 1), Preadditive.comp_sum]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f :
    toTopRep.obj ((Monad.coresolution (coindMonad.{u, w} G) A).obj (SimplexCategory.mk n)) ⟶
      TopRep.resolutionX (toTopRep.obj A) (n + 2) => (-1 : ℤ) ^ i.val • f)
    (coindCoresolution_coface.{u, w} G A n i)

private theorem alternatingComplexSuccessor {C : Type u₀} [Category.{v₀} C]
    [Preadditive C] (X : CosimplicialObject C) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X n := by
  dsimp only [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  exact CochainComplex.of_d (fun i => X.obj (SimplexCategory.mk i))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD X) n

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let L_A be the alternating-coface cochain complex of J(K_A),
indexed by ℕ, and let R'_A have term R_{n+1}(JA) in degree n and differential d_{JA}(n+1). For
every n≥0, L_A.d_{n,n+1}≫(e_A^{n+1}).hom=(e_A^n).hom≫R'_A.d_{n,n+1}, where e_A^n is the
coresolution term comparison. -/
theorem coindCoresolution_complex_differential (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep)).d n (n + 1) ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫
        (TopRep.resolution' (toTopRep.obj A)).d n (n + 1) := by
  have hs := alternatingComplexSuccessor
    ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) n
  have ht : (TopRep.resolution' (toTopRep.obj A)).d n (n + 1) =
      TopRep.d (toTopRep.obj A) (n + 1) := CochainComplex.of_d _ _ n
  exact (congrArg (fun f => f ≫ (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom) hs).trans
    ((coindCoresolution_differential.{u, w} G A n).trans
      (congrArg (fun f => (coindCoresolutionTermIso.{u, w} G A n).hom ≫ f) ht.symm))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). The alternating-coface complex of J(K_A) is isomorphic to the
nonnegative cochain complex R'_A with degree-n term R_{n+1}(JA) and differential
Σ_{i=0}^{n+1}(-1)^i c_i^{n+1}. The degree-n component is e_A^n:J(K_A^n)≅R_{n+1}(JA), for every
n≥0. -/
def coindCoresolutionComplexIso (A : DiscreteAbelianAction.{u, max u w} G) :
    (AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) ≅
      TopRep.resolution' (toTopRep.obj A) :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := (AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
      ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep))
    (C₂ := TopRep.resolution' (toTopRep.obj A))
    (coindCoresolutionTermIso.{u, w} G A)
    (fun i j hij => by
      change i + 1 = j at hij
      subst j
      exact (coindCoresolution_complex_differential.{u, w} G A i).symm)

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). The
equivariant continuous additive map Δ_X:C(CX)→CX evaluates a nested function on the diagonal:
(Δ_X F)(g)=F(g)(g). Its continuity uses the diagonal G→G×G and the continuous uncurrying of
continuous functions on the compact group. -/
def coindResolutionDiagonal (X : TopRep.{max u w, 0, u} ℤ G) : X.coind₁.coind₁ ⟶ X.coind₁ := by
  letI : Module ℤ X := X.hV2
  letI : Module ℤ X.coind₁ := X.coind₁.hV2
  letI : Module ℤ X.coind₁.coind₁ := X.coind₁.coind₁.hV2
  let δ : C(G, G × G) := ⟨fun g => (g, g), continuous_id.prodMk continuous_id⟩
  exact TopRep.ofHom
    { toFun := fun z => (ContinuousMap.uncurry z).comp δ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun _ => rfl
      cont := (ContinuousMap.continuous_precomp δ).comp ContinuousMap.continuous_uncurry }

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For
F∈C(CX) and g∈G, the diagonal morphism Δ_X:C(CX)→CX satisfies (Δ_X F)(g)=F(g)(g). This formula
uses the same group element in the outer and inner function coordinates. -/
theorem coindResolutionDiagonal_apply (X : TopRep.{max u w, 0, u} ℤ G)
    (z : X.coind₁.coind₁) (g : G) :
    ((coindResolutionDiagonal.{u, w} G X).hom z) g = z g g := rfl

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For a
continuous equivariant ℤ-linear map f:X→Y, the diagonal morphisms obey C(Cf)≫Δ_Y=Δ_X≫C(f). Both
paths take F:G→C(G,X) to the function g↦f(F(g)(g)). -/
theorem coindResolutionDiagonal_naturality {X Y : TopRep.{max u w, 0, u} ℤ G}
    (f : X ⟶ Y) :
    (TopRep.coind₁Functor ℤ G).map ((TopRep.coind₁Functor ℤ G).map f) ≫
        coindResolutionDiagonal.{u, w} G Y =
      coindResolutionDiagonal.{u, w} G X ≫ (TopRep.coind₁Functor ℤ G).map f := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let j_A:J(TA)≅C(JA), μ_A:T(TA)→TA, and Δ_{JA}:C(C(JA))→C(JA) be
diagonal evaluation. The comparison of multiplication is
J(μ_A)≫j_A.hom=j_{TA}.hom≫C(j_A.hom)≫Δ_{JA}. It sends F to g↦F(g)(g). -/
theorem coindToTopRepIso_mul (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((coindMonad.{u, w} G).μ.app A) ≫ (coindToTopRepIso.{u, w} G A).hom =
      (coindToTopRepIso.{u, w} G (coind.{u, w}.obj A)).hom ≫
        (TopRep.coind₁Functor ℤ G).map (coindToTopRepIso.{u, w} G A).hom ≫
        coindResolutionDiagonal.{u, w} G (toTopRep.obj A) := by
  let : Module ℤ (toTopRep.obj
      (((coindMonad.{u, w} G).toFunctor ⋙ (coindMonad.{u, w} G).toFunctor).obj A)) :=
    (toTopRep.obj
      (((coindMonad.{u, w} G).toFunctor ⋙ (coindMonad.{u, w} G).toFunctor).obj A)).hV2
  let : Module ℤ (toTopRep.obj A).coind₁ := (toTopRep.obj A).coind₁.hV2
  apply TopRep.hom_ext
  refine ContIntertwiningMap.ext ?_
  refine ContinuousLinearMap.ext (fun z => ?_)
  refine ContinuousMap.ext (fun g => ?_)
  exact coindMonad_mul_apply.{u, w} G A z g

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0
and 0≤i<n, s_i^n:R_{n+1}(X)→R_n(X) repeats the i-th function coordinate in two adjacent
positions. The family in degree zero is empty; s_0^{n+1}=Δ_{R_n(X)}, and s_{i+1}^{n+1}=C(s_i^n). -/
def coindResolutionCodegeneracy (X : TopRep.{max u w, 0, u} ℤ G) :
    (n : ℕ) → Fin n → (TopRep.resolutionX X (n + 1) ⟶ TopRep.resolutionX X n)
  | 0, i => Fin.elim0 i
  | n + 1, ⟨0, _⟩ => coindResolutionDiagonal.{u, w} G (TopRep.resolutionX X n)
  | n + 1, ⟨i + 1, hi⟩ =>
      (TopRep.coind₁Functor ℤ G).map
        (coindResolutionCodegeneracy X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0,
the first codegeneracy s_0^{n+1}:R_{n+2}(X)→R_{n+1}(X) equals Δ_{R_n(X)}. A function of two
outer coordinates is evaluated with those coordinates equal, while all n inner coordinates are
retained. -/
theorem coindResolutionCodegeneracy_zero (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    coindResolutionCodegeneracy.{u, w} G X (n + 1) 0 =
      coindResolutionDiagonal.{u, w} G (TopRep.resolutionX X n) := rfl

omit [TotallyDisconnectedSpace G] in
/-- Let G be a compact topological group in universe u and X a continuous ℤ-representation with
coefficient universe W=max(u,w). Write C for continuous coinduction and R_n(X)=C^n(X). For n≥0
and 0≤i≤n, the codegeneracy recursion is s_{i+1}^{n+2}=C(s_i^{n+1}). Since
s_i^{n+1}:R_{n+2}(X)→R_{n+1}(X), its coinduction merges the next pair of adjacent coordinates
inside the outer coordinate. -/
theorem coindResolutionCodegeneracy_succ (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ)
    (i : Fin (n + 1)) :
    coindResolutionCodegeneracy.{u, w} G X (n + 2) i.succ =
      (TopRep.coind₁Functor ℤ G).map (coindResolutionCodegeneracy.{u, w} G X (n + 1) i) := rfl

private theorem barMuZeroInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (A : C) :
    Monad.barMuAtPos T (n + 1) 0 A ≫ eqToHom (Monad.monadPow_succ_obj_eq T n A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) ≫
        T.map (eqToHom (Monad.monadPow_succ_obj_eq T n A)) ≫
        T.μ.app ((Monad.monadPow T n).obj A) := by
  simp only [Monad.barMuAtPos, Fin.rev_zero]
  induction n generalizing A with
  | zero =>
      change T.μ.app A ≫ 𝟙 _ = 𝟙 _ ≫ T.map (𝟙 (T.obj A)) ≫ T.μ.app A
      rw [Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  | succ n ih => exact ih (T.obj A)

private theorem muCastSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.muAtPos T (n + 2) i.castSucc A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 2) A) ≫
        T.map (Monad.muAtPos T (n + 1) i A) := by
  induction n generalizing A with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact Monad.monadPow_obj_T_comm_naturality T 0 (T.μ.app A)
  | succ n ih =>
      cases i with
      | mk val hval =>
          cases val with
          | zero => exact Monad.monadPow_obj_T_comm_naturality T (n + 1) (T.μ.app A)
          | succ k => exact ih ⟨k, Nat.lt_of_succ_lt_succ hval⟩ (T.obj A)

private theorem barMuSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.barMuAtPos T (n + 2) i.succ A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 2) A) ≫
        T.map (Monad.barMuAtPos T (n + 1) i A) := by
  simp only [Monad.barMuAtPos, Fin.rev_succ]
  exact muCastSuccInPowers T n i.rev A

private def mapIntoDoubleSource {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (P Q : C) (e : Q ⟶ T.obj P) :
    L.obj (T.obj Q) ⟶ L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) := L.map (T.map e)

private theorem mapIntoDoubleSource_eq {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (P Q : C) (e : Q ⟶ T.obj P) :
    mapIntoDoubleSource T L P Q e = L.map (T.map e) := rfl

private theorem mappedBarMuZero {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D) (n : ℕ) (A : C) :
    L.map (Monad.barMuAtPos T (n + 1) 0 A) ≫
        L.map (eqToHom (Monad.monadPow_succ_obj_eq T n A)) =
      L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫
        CategoryStruct.comp
          (Y := L.obj ((T.toFunctor ⋙ T.toFunctor).obj ((Monad.monadPow T n).obj A)))
          (mapIntoDoubleSource T L ((Monad.monadPow T n).obj A)
            ((Monad.monadPow T (n + 1)).obj A)
            (eqToHom (Monad.monadPow_succ_obj_eq T n A)))
          (L.map (T.μ.app ((Monad.monadPow T n).obj A))) := by
  exact ((Functor.map_comp L _ _).symm.trans
    ((congrArg (fun f => L.map f) (barMuZeroInPowers T n A)).trans
      ((Functor.map_comp L _ _).trans
        (congrArg (fun f => L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫ f)
          (Functor.map_comp L _ _))))).trans
    (congrArg (fun b => L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫
        b ≫ L.map (T.μ.app ((Monad.monadPow T n).obj A)))
      (mapIntoDoubleSource_eq T L ((Monad.monadPow T n).obj A)
        ((Monad.monadPow T (n + 1)).obj A)
        (eqToHom (Monad.monadPow_succ_obj_eq T n A))).symm)

private theorem mappedBarMuSucc {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (n : ℕ) (i : Fin (n + 1)) (A : C) :
    L.map (Monad.barMuAtPos T (n + 1 + 1) i.succ A) ≫
        L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) =
      L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1 + 1) A)) ≫
        L.map (T.map (Monad.barMuAtPos T (n + 1) i A)) := by
  exact (Functor.map_comp L _ _).symm.trans
    ((congrArg (fun f => L.map f) (barMuSuccInPowers T n i A)).trans
      (Functor.map_comp L _ _))

private theorem diagonalFunctorComposite {C : Type u₀} [Category.{v₀} C]
    (F : C ⥤ C) {P Q Q' BP BQ BBP N : C}
    (m : Q' ⟶ Q) (E₀ : Q ⟶ BP) (E₁ : Q' ⟶ BQ)
    (B : BQ ⟶ BBP) (M : BBP ⟶ BP)
    (J₀ : BP ⟶ F.obj P) (J₁ : BQ ⟶ F.obj Q) (J₂ : BBP ⟶ F.obj BP)
    (I₀ : P ⟶ N) (D₀ : F.obj (F.obj P) ⟶ F.obj P)
    (D₁ : F.obj (F.obj N) ⟶ F.obj N)
    (hp : m ≫ E₀ = E₁ ≫ B ≫ M)
    (hu : M ≫ J₀ = J₂ ≫ F.map J₀ ≫ D₀)
    (hj : B ≫ J₂ = J₁ ≫ F.map E₀)
    (hd : D₀ ≫ F.map I₀ = F.map (F.map I₀) ≫ D₁) :
    m ≫ (E₀ ≫ J₀ ≫ F.map I₀) = (E₁ ≫ J₁ ≫ F.map (E₀ ≫ J₀ ≫ F.map I₀)) ≫ D₁ := by
  calc
    _ = ((m ≫ E₀) ≫ J₀) ≫ F.map I₀ := by simp only [Category.assoc]
    _ = ((E₁ ≫ B ≫ M) ≫ J₀) ≫ F.map I₀ := congrArg (fun f => (f ≫ J₀) ≫ F.map I₀) hp
    _ = E₁ ≫ B ≫ (M ≫ J₀) ≫ F.map I₀ := by simp only [Category.assoc]
    _ = E₁ ≫ B ≫ (J₂ ≫ F.map J₀ ≫ D₀) ≫ F.map I₀ :=
      congrArg (fun f => E₁ ≫ B ≫ f ≫ F.map I₀) hu
    _ = E₁ ≫ (B ≫ J₂) ≫ F.map J₀ ≫ D₀ ≫ F.map I₀ := by simp only [Category.assoc]
    _ = E₁ ≫ (J₁ ≫ F.map E₀) ≫ F.map J₀ ≫ D₀ ≫ F.map I₀ :=
      congrArg (fun f => E₁ ≫ f ≫ F.map J₀ ≫ D₀ ≫ F.map I₀) hj
    _ = E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ (D₀ ≫ F.map I₀) := by simp only [Category.assoc]
    _ = E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ (F.map (F.map I₀) ≫ D₁) :=
      congrArg (fun f => E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ f) hd
    _ = (E₁ ≫ J₁ ≫ (F.map E₀ ≫ F.map J₀ ≫ F.map (F.map I₀))) ≫ D₁ := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun f => (E₁ ≫ J₁ ≫ f) ≫ D₁)
      ((Functor.map_comp F E₀ (J₀ ≫ F.map I₀)).trans
        (congrArg (fun f => F.map E₀ ≫ f) (Functor.map_comp F J₀ (F.map I₀)))).symm

private theorem diagonalFunctionComposite {ι : Type u₀}
    {P Q Q' BP BQ BBP N : Type v₀}
    (m : Q' → Q) (E₀ : Q → BP) (E₁ : Q' → BQ) (B : BQ → BBP) (M : BBP → BP)
    (J₀ : BP → ι → P) (J₁ : BQ → ι → Q) (J₂ : BBP → ι → BP) (I₀ : P → N)
    (hp : ∀ x, E₀ (m x) = M (B (E₁ x)))
    (hu : ∀ y i, J₀ (M y) i = J₀ (J₂ y i) i)
    (hj : ∀ y i, J₂ (B y) i = E₀ (J₁ y i)) (x : Q') (i : ι) :
    I₀ (J₀ (E₀ (m x)) i) = I₀ (J₀ (E₀ (J₁ (E₁ x) i)) i) :=
  (congrArg (fun y => I₀ (J₀ y i)) (hp x)).trans
    ((congrArg I₀ (hu (B (E₁ x)) i)).trans
      (congrArg (fun y => I₀ (J₀ y i)) (hj (E₁ x) i)))

private theorem transferExpandedSquare {C : Type u₀} [Category.{v₀} C]
    {R Q X Y : C} (m : R ⟶ Q) (l l₀ : Q ⟶ X) (r r₀ : R ⟶ Y) (d : Y ⟶ X)
    (h : m ≫ l₀ = r₀ ≫ d) (hl : l = l₀) (hr : r = r₀) : m ≫ l = r ≫ d :=
  (congrArg (fun f => m ≫ f) hl).trans (h.trans (congrArg (fun f => f ≫ d) hr.symm))

private theorem transferSquareTarget {C : Type u₀} [Category.{v₀} C]
    {R Q X Y : C} (m : R ⟶ Q) (l l₀ : Q ⟶ X) (r r₀ : R ⟶ Y) (d d₀ : Y ⟶ X)
    (h : m ≫ l₀ = r₀ ≫ d₀) (hl : l = l₀) (hr : r = r₀) (hd : d = d₀) :
    m ≫ l = r ≫ d :=
  (transferExpandedSquare m l l₀ r r₀ d₀ h hl hr).trans
    (congrArg (fun f => r ≫ f) hd.symm)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem topRepTwoThreeValueEq {A₀ A₁ A₂ A₃ A₄ : TopRep.{max u w, 0, u} ℤ G}
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₄) (h : A₀ ⟶ A₂)
    (i : A₂ ⟶ A₃) (j : A₃ ⟶ A₄) (heq : f ≫ g = h ≫ i ≫ j) (x : A₀) :
    g.hom (f.hom x) = j.hom (i.hom (h.hom x)) :=
  congrArg (fun k : A₀ ⟶ A₄ => k.hom x) heq

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem topRepTwoTwoValueEq {A₀ A₁ A₂ A₃ : TopRep.{max u w, 0, u} ℤ G}
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₃) (h : A₀ ⟶ A₂)
    (i : A₂ ⟶ A₃) (heq : f ≫ g = h ≫ i) (x : A₀) :
    g.hom (f.hom x) = i.hom (h.hom x) :=
  congrArg (fun k : A₀ ⟶ A₃ => k.hom x) heq

private def coindMonadToTopRepHom (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.obj ((coindMonad.{u, w} G).obj A) ⟶
      (TopRep.coind₁Functor ℤ G).obj (toTopRep.obj A) := by
  change toTopRep.obj (coind.{u, w}.obj A) ⟶ (toTopRep.obj A).coind₁
  exact (coindToTopRepIso.{u, w} G A).hom

private theorem coindMonadToTopRepHom_eq (A : DiscreteAbelianAction.{u, max u w} G) :
    coindMonadToTopRepHom.{u, w} G A = (coindToTopRepIso.{u, w} G A).hom := by
  rfl

private theorem coindMappedBarMuZero (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A) ≫
        toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A)) ≫
        mapIntoDoubleSource (coindMonad.{u, w} G) (toTopRep.{u, max u w} (G := G))
          ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
            toTopRep.map ((coindMonad.{u, w} G).μ.app
              ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) := by
  with_reducible exact (mappedBarMuZero (coindMonad.{u, w} G)
    (toTopRep.{u, max u w} (G := G)) n A)

private theorem coindDiagonalTypedSquare
    (P Q R : DiscreteAbelianAction.{u, max u w} G)
    (N : TopRep.{max u w, 0, u} ℤ G)
    (m : R ⟶ Q)
    (e₀ : Q ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : R ⟶ (coindMonad.{u, w} G).obj Q)
    (I₀ : toTopRep.obj P ⟶ N)
    (hp :
      toTopRep.map m ≫ toTopRep.map e₀ =
        toTopRep.map e₁ ≫
          mapIntoDoubleSource (coindMonad.{u, w} G)
            (toTopRep.{u, max u w} (G := G)) P Q e₀ ≫
          toTopRep.map ((coindMonad.{u, w} G).μ.app P)) :
    toTopRep.map m ≫
        (toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
          (TopRep.coind₁Functor ℤ G).map I₀) =
      (toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
        (TopRep.coind₁Functor ℤ G).map
          (toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
            (TopRep.coind₁Functor ℤ G).map I₀)) ≫
        coindResolutionDiagonal.{u, w} G N := by
  let T : Monad (DiscreteAbelianAction.{u, max u w} G) := coindMonad.{u, w} G
  let L : DiscreteAbelianAction.{u, max u w} G ⥤ TopRep.{max u w, 0, u} ℤ G :=
    toTopRep.{u, max u w} (G := G)
  let F : TopRep.{max u w, 0, u} ℤ G ⥤ TopRep.{max u w, 0, u} ℤ G :=
    TopRep.coind₁Functor ℤ G
  let m₀ : L.obj R ⟶ L.obj Q := L.map m
  let E₀ : L.obj Q ⟶ L.obj (T.obj P) := L.map e₀
  let E₁ : L.obj R ⟶ L.obj (T.obj Q) := L.map e₁
  let B : L.obj (T.obj Q) ⟶ L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) :=
    mapIntoDoubleSource T L P Q e₀
  let M : L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) ⟶ L.obj (T.obj P) :=
    L.map (T.μ.app P)
  let J₀ : L.obj (T.obj P) ⟶ F.obj (L.obj P) := coindMonadToTopRepHom.{u, w} G P
  let J₁ : L.obj (T.obj Q) ⟶ F.obj (L.obj Q) := coindMonadToTopRepHom.{u, w} G Q
  let J₂ : L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) ⟶ F.obj (L.obj (T.obj P)) := by
    change L.obj (T.obj (T.obj P)) ⟶ F.obj (L.obj (T.obj P))
    exact coindMonadToTopRepHom.{u, w} G (T.obj P)
  let D₀ : F.obj (F.obj (L.obj P)) ⟶ F.obj (L.obj P) :=
    coindResolutionDiagonal.{u, w} G (L.obj P)
  let D₁ : F.obj (F.obj N) ⟶ F.obj N := coindResolutionDiagonal.{u, w} G N
  have hu : M ≫ J₀ = J₂ ≫ F.map J₀ ≫ D₀ := coindToTopRepIso_mul.{u, w} G P
  have hj : B ≫ J₂ = J₁ ≫ F.map E₀ := coindToTopRepIso_naturality.{u, w} G e₀
  have hd : D₀ ≫ F.map I₀ = F.map (F.map I₀) ≫ D₁ :=
    (coindResolutionDiagonal_naturality.{u, w} G I₀).symm
  exact diagonalFunctorComposite
    (C := TopRep.{max u w, 0, u} ℤ G) F
    (P := L.obj P) (Q := L.obj Q) (Q' := L.obj R)
    (BP := L.obj (T.obj P)) (BQ := L.obj (T.obj Q))
    (BBP := L.obj ((T.toFunctor ⋙ T.toFunctor).obj P)) (N := N)
    m₀ E₀ E₁ B M J₀ J₁ J₂ I₀ D₀ D₁ hp hu hj hd


private theorem coindDiagonalFullTypedSquare
    (P Q R : DiscreteAbelianAction.{u, max u w} G)
    (N : TopRep.{max u w, 0, u} ℤ G)
    (m : R ⟶ Q)
    (e₀ : Q ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : R ⟶ (coindMonad.{u, w} G).obj Q)
    (I₀ : toTopRep.obj P ⟶ N)
    (I₁ : toTopRep.obj Q ⟶ (TopRep.coind₁Functor ℤ G).obj N)
    (I₂ : toTopRep.obj R ⟶ (TopRep.coind₁Functor ℤ G).obj ((TopRep.coind₁Functor ℤ G).obj N))
    (hp :
      toTopRep.map m ≫ toTopRep.map e₀ =
        toTopRep.map e₁ ≫
          mapIntoDoubleSource (coindMonad.{u, w} G)
            (toTopRep.{u, max u w} (G := G)) P Q e₀ ≫
          toTopRep.map ((coindMonad.{u, w} G).μ.app P))
    (h₀ : I₁ = toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
      (TopRep.coind₁Functor ℤ G).map I₀)
    (h₁ : I₂ = toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
      (TopRep.coind₁Functor ℤ G).map I₁) :
    toTopRep.map m ≫ I₁ = I₂ ≫ coindResolutionDiagonal.{u, w} G N := by
  let L := toTopRep.{u, max u w} (G := G)
  let F := TopRep.coind₁Functor ℤ G
  let l₀ := L.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫ F.map I₀
  let r₀ := L.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫ F.map l₀
  have h := coindDiagonalTypedSquare.{u, w} G P Q R N m e₀ e₁ I₀ hp
  have hr : I₂ = r₀ := h₁.trans
    (congrArg (fun f : L.obj Q ⟶ F.obj N =>
      (show L.obj R ⟶ F.obj (F.obj N) from L.map e₁ ≫
        coindMonadToTopRepHom.{u, w} G Q ≫ F.map f)) h₀)
  exact transferExpandedSquare (L.map m) I₁ l₀ I₂ r₀
    (coindResolutionDiagonal.{u, w} G N) h h₀ hr

private def coindPowerSuccNativeHom (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A) ⟶
      (TopRep.coind₁Functor ℤ G).obj (TopRep.resolutionX (toTopRep.obj A) n) :=
  (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom

private theorem coindPowerSuccNativeHom_eq (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    coindPowerSuccNativeHom.{u, w} G A n =
      (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := rfl

private theorem coindPowerSuccHomNormalized (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
        coindMonadToTopRepHom.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≫
          (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := by
  let L := toTopRep.{u, max u w} (G := G)
  let E := L.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
  let F := TopRep.coind₁Functor ℤ G
  let I := (coindPowerToTopRepIso.{u, w} G A n).hom
  exact (coindPowerToTopRepIso_succ_hom.{u, w} G A n).trans
    (congrArg (fun j => E ≫ j ≫ F.map I)
      (coindMonadToTopRepHom_eq.{u, w} G
        ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).symm)

private theorem coindPowerSuccNativeHom_normalized
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    coindPowerSuccNativeHom.{u, w} G A n =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
        coindMonadToTopRepHom.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≫
          (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
  (coindPowerSuccNativeHom_eq.{u, w} G A n).trans
    (coindPowerSuccHomNormalized.{u, w} G A n)

private theorem coindMapFullTypedSquare
    (P Q R S : DiscreteAbelianAction.{u, max u w} G)
    (NP NQ : TopRep.{max u w, 0, u} ℤ G) (φ : P ⟶ Q) (m : R ⟶ S)
    (e₀ : R ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : S ⟶ (coindMonad.{u, w} G).obj Q)
    (IP : toTopRep.obj P ⟶ NP) (IQ : toTopRep.obj Q ⟶ NQ)
    (IR : toTopRep.obj R ⟶ (TopRep.coind₁Functor ℤ G).obj NP)
    (IS : toTopRep.obj S ⟶ (TopRep.coind₁Functor ℤ G).obj NQ) (d : NP ⟶ NQ)
    (hp : toTopRep.map m ≫ toTopRep.map e₁ =
      toTopRep.map e₀ ≫ toTopRep.map ((coindMonad.{u, w} G).map φ))
    (hI : toTopRep.map φ ≫ IQ = IP ≫ d)
    (hR : IR = toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
      (TopRep.coind₁Functor ℤ G).map IP)
    (hS : IS = toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
      (TopRep.coind₁Functor ℤ G).map IQ) :
    toTopRep.map m ≫ IS = IR ≫ (TopRep.coind₁Functor ℤ G).map d := by
  let L := toTopRep.{u, max u w} (G := G)
  let F := TopRep.coind₁Functor ℤ G
  let J₀ := coindMonadToTopRepHom.{u, w} G P
  let J₁ := coindMonadToTopRepHom.{u, w} G Q
  have hj : L.map ((coindMonad.{u, w} G).map φ) ≫ J₁ = J₀ ≫ F.map (L.map φ) :=
    coindToTopRepIso_naturality.{u, w} G φ
  have hh : F.map (L.map φ) ≫ F.map IQ = F.map IP ≫ F.map d :=
    (Functor.map_comp F (L.map φ) IQ).symm.trans
      ((congrArg (fun f => F.map f) hI).trans (Functor.map_comp F IP d))
  have he := threeSquareComposite (L.map m) (L.map ((coindMonad.{u, w} G).map φ))
    (F.map (L.map φ)) (F.map d) (L.map e₀) (L.map e₁) J₀ J₁
    (F.map IP) (F.map IQ) hp hj hh
  exact transferExpandedSquare (L.map m) IS (L.map e₁ ≫ J₁ ≫ F.map IQ)
    IR (L.map e₀ ≫ J₀ ≫ F.map IP) (F.map d) he hS hR

set_option backward.isDefEq.respectTransparency.types true in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For n≥0, let m_0^{n+1}:T^{n+2}A→T^{n+1}A be the outer
multiplication insertion. Then J(m_0^{n+1})≫(E_A^{n+1}).hom=(E_A^{n+2}).hom≫Δ_{R_n(JA)}. The
right side repeats the outer two homogeneous function coordinates. -/
theorem coindPowerToTopRepIso_codegeneracy_zero
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
        coindResolutionDiagonal.{u, w} G (TopRep.resolutionX (toTopRep.obj A) n) := by
  exact coindDiagonalFullTypedSquare.{u, w} G
    ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
    ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
    ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
    (TopRep.resolutionX (toTopRep.obj A) n)
    (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A)
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))
    (coindPowerToTopRepIso.{u, w} G A n).hom
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom
    (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
    (coindMappedBarMuZero.{u, w} G A n)
    (coindPowerSuccHomNormalized.{u, w} G A n)
    (coindPowerSuccHomNormalized.{u, w} G A (n + 1))

set_option backward.isDefEq.respectTransparency.types true in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For n≥0 and 0≤i≤n, let m_i^{n+1}:T^{n+2}A→T^{n+1}A be
multiplication in codegeneracy position i. Then
J(m_i^{n+1})≫(E_A^{n+1}).hom=(E_A^{n+2}).hom≫s_i^{n+1}, where s_i^{n+1}:R_{n+2}(JA)→R_{n+1}(JA)
repeats adjacent coordinates. -/
theorem coindPowerToTopRepIso_codegeneracy
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
        coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i := by
  induction n with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      simpa only [coindResolutionCodegeneracy_zero] using
        coindPowerToTopRepIso_codegeneracy_zero.{u, w} G A 0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [coindResolutionCodegeneracy_zero] using
          coindPowerToTopRepIso_codegeneracy_zero.{u, w} G A (n + 1)
      · let φ := Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) j A
        have h := coindMapFullTypedSquare.{u, w} G
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1 + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
          (TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1))
          (TopRep.resolutionX (toTopRep.obj A) (n + 1)) φ
          (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1 + 1) j.succ A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1 + 1) A))
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1 + 1))
          (coindPowerSuccNativeHom.{u, w} G A (n + 1))
          (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) j)
          (mappedBarMuSucc (coindMonad.{u, w} G) (toTopRep.{u, max u w} (G := G)) n j A) (ih j)
          (by with_reducible exact (coindPowerSuccNativeHom_normalized.{u, w} G A (n + 1 + 1)))
          (by with_reducible exact (coindPowerSuccNativeHom_normalized.{u, w} G A (n + 1)))
        have hResult := transferSquareTarget (C := TopRep.{max u w, 0, u} ℤ G)
          (R := toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1 + 1)).obj A))
          (Q := toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A))
          (X := TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1))
          (Y := TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1 + 1))
          (toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1 + 1) j.succ A))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1 + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1 + 1))
          (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1 + 1) j.succ)
          ((TopRep.coind₁Functor ℤ G).map
            (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) j))
          (by with_reducible exact h)
          (by with_reducible exact (coindPowerSuccNativeHom_eq.{u, w} G A (n + 1)).symm)
          (by with_reducible exact (coindPowerSuccNativeHom_eq.{u, w} G A (n + 1 + 1)).symm)
          (by with_reducible exact (coindResolutionCodegeneracy_succ.{u, w} G (toTopRep.obj A) n j))
        exact hResult

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let e_A^n:J(K_A^n)≅R_{n+1}(JA) compare the monad coresolution
terms. For n≥0 and 0≤i≤n, the cosimplicial codegeneracy σ_i:K_A^{n+1}→K_A^n obeys
J(σ_i)≫(e_A^n).hom=(e_A^{n+1}).hom≫s_i^{n+1}. -/
theorem coindCoresolution_codegeneracy (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i)) ≫
        (coindCoresolutionTermIso.{u, w} G A n).hom =
      (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom ≫
        coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i := by
  rw [coindCoresolutionTermIso_hom, coindCoresolutionTermIso_hom]
  have hc := (Functor.map_comp toTopRep
    ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i))
    (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom).symm.trans
      ((congrArg (fun f => toTopRep.map f)
        (Monad.coresolutionObjIso_codegeneracy (coindMonad.{u, w} G) A i)).trans
          (Functor.map_comp toTopRep (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom
            (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A)))
  have hp := coindPowerToTopRepIso_codegeneracy.{u, w} G A n i
  calc
    _ = (toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i)) ≫
        toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := (Category.assoc _ _ _).symm
    _ = (toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A)) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom :=
      congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom) hc
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        (toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom) := Category.assoc _ _ _
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        ((coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
          coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i) :=
      congrArg (fun f => toTopRep.map
        (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫ f) hp
    _ = _ := (Category.assoc _ _ _).symm

private theorem coresolutionZeroCoordinates {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (A : C) :
    (Monad.coresolutionObjIso T A 0).hom = 𝟙 (T.obj A) := by
  rw [Monad.coresolutionObjIso_hom]
  rfl

private theorem coindPowerOneHom (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindPowerToTopRepIso.{u, w} G A 1).hom = (coindToTopRepIso.{u, w} G A).hom := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). The degree-zero monad coresolution term is TA. Its comparison
e_A^0:J(K_A^0)≅R_1(JA)=C(JA) satisfies (e_A^0).hom=j_A.hom, where j_A:J(TA)≅C(JA) preserves
continuous function values. -/
theorem coindCoresolutionTermIso_zero_hom (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindCoresolutionTermIso.{u, w} G A 0).hom = (coindToTopRepIso.{u, w} G A).hom := by
  let L := toTopRep.{u, max u w} (G := G)
  rw [coindCoresolutionTermIso_hom]
  have hc := (congrArg (fun f => L.map f)
    (coresolutionZeroCoordinates (coindMonad.{u, w} G) A)).trans
      (Functor.map_id L ((coindMonad.{u, w} G).obj A))
  exact (congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A 1).hom) hc).trans
    ((Category.id_comp _).trans (coindPowerOneHom.{u, w} G A))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). Let a_A:A→K_A^0 be the degree-zero coaugmentation of the
augmented monad coresolution. Its term comparison e_A^0:J(K_A^0)≅C(JA) satisfies
J(a_A)≫(e_A^0).hom=ι_{JA}, the continuous constant-function inclusion JA→C(JA). -/
theorem coindCoresolution_coaugmentation (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((Monad.coresolutionAugmented (coindMonad.{u, w} G) A).hom.app
      (SimplexCategory.mk 0)) ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom =
        (TopRep.coind₁ι (k := ℤ) (G := G)).app (toTopRep.obj A) := by
  let L := toTopRep.{u, max u w} (G := G)
  have ha := congrArg (fun f => L.map f)
    (Monad.coresolutionAugmented_hom_zero (coindMonad.{u, w} G) A)
  have ht := coindCoresolutionTermIso_zero_hom.{u, w} G A
  exact (congrArg (fun f => f ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom) ha).trans
    ((congrArg (fun f => L.map ((coindMonad.{u, w} G).η.app A) ≫ f) ht).trans
      (coindToTopRepIso_unit.{u, w} G A))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Write T for diagonal continuous
coinduction, J for the functor to continuous ℤ-representations, C for representation
coinduction, and R_n(X)=C^n(X). For the degree-zero coaugmentation a_A:A→K_A^0 and comparison
e_A^0:J(K_A^0)≅C(JA), every a∈A and g∈G satisfy ((J(a_A)≫(e_A^0).hom)(a))(g)=a. The coefficient
does not depend on the group coordinate. -/
theorem coindCoresolution_coaugmentation_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (a : underlying A) (g : G) :
    ((toTopRep.map ((Monad.coresolutionAugmented (coindMonad.{u, w} G) A).hom.app
      (SimplexCategory.mk 0)) ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom).hom a) g = a := by
  have h := congrArg (fun f : toTopRep.obj A ⟶ (toTopRep.obj A).coind₁ => f.hom a g)
    (coindCoresolution_coaugmentation.{u, w} G A)
  exact h.trans rfl

end CategoryTheory.DiscreteAbelianAction
