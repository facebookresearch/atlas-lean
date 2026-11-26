/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exactness by finite descent through submodule families

Let R be a ring and e : A →ₗ[R] B, d : B →ₗ[R] C maps preserving submodule families
P_p,F_p,H_p. The adjacent quotient of F is F_{p+1}/(F_p∩F_{p+1}), with the intersection
considered inside F_{p+1}; for an increasing family this is F_{p+1}/F_p.

Exactness of the induced quotient sequence lets a cycle in F_{p+1} be modified by a boundary
from P_{p+1} so that its remainder lies in F_p. If de=0, F_0=0, every element of B lies in
some F_p, and every adjacent quotient sequence is exact, finite descent proves
range(e)=ker(d). Monotonicity of the families and exhaustiveness of P or H are not hypotheses
of this statement.
-/

@[expose] public section

universe u v w t

variable {R : Type u} [Ring R]

namespace Submodule

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Let R be a ring, M an R-module, F : ℕ → Submodule R M, and p ∈ ℕ. Define a submodule of
F_{p+1} by {x ∈ F_{p+1} | x ∈ F_p}, equivalently the inverse image of F_p under the subtype
inclusion F_{p+1} → M. If F is increasing, this is F_p viewed inside F_{p+1}; the definition
itself requires no monotonicity. -/
def filtrationLower (F : ℕ → Submodule R M) (p : ℕ) : Submodule R (F (p + 1)) :=
  (F p).comap (F (p + 1)).subtype

/-- For a module M over a ring R, a family F : ℕ → Submodule R M, and p ∈ ℕ, define
FiltrationLayer(F,p) = F_{p+1}/(F_p∩F_{p+1}), with the denominator viewed as a submodule of
F_{p+1}. For an increasing family this is the usual adjacent quotient F_{p+1}/F_p. No
monotonicity is needed to form the quotient. -/
abbrev FiltrationLayer (F : ℕ → Submodule R M) (p : ℕ) :=
  F (p + 1) ⧸ filtrationLower F p

end Submodule

namespace LinearMap

variable {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type w} [AddCommGroup B] [Module R B]
  {C : Type t} [AddCommGroup C] [Module R C]

/-- Let R be a ring, f : A →ₗ[R] B an R-linear map, and F,G families of submodules of A,B. Assume
f(F_p) ⊆ G_p for every p ∈ ℕ. Then for a fixed p, f restricts to an R-linear map F_p → G_p,
taking a stage element x to f(x) with its given membership in G_p. The module carriers may
have independent universes. -/
def filtrationStage (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) : F p →ₗ[R] G p where
  toFun x := ⟨f x, hf p x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact f.map_smul r x

@[simp]
theorem filtrationStage_apply (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) (x : F p) :
    (f.filtrationStage F G hf p x).val = f x.val := rfl

/-- Let R be a ring, f : A →ₗ[R] B, and F,G submodule families with f(F_p) ⊆ G_p for every p. The
restriction on stage p+1 induces an R-linear map F_{p+1}/(F_p∩F_{p+1}) →
G_{p+1}/(G_p∩G_{p+1}). It sends the quotient class of x to the class of f(x). Preservation of
both p and p+1 makes this quotient map well defined; no monotonicity assumption is needed. -/
def filtrationLayerMap (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) :
    Submodule.FiltrationLayer F p →ₗ[R] Submodule.FiltrationLayer G p :=
  Submodule.mapQ (Submodule.filtrationLower F p) (Submodule.filtrationLower G p)
    (f.filtrationStage F G hf (p + 1)) (by
      intro x hx
      exact hf p x.val hx)

@[simp]
theorem filtrationLayerMap_mkQ (f : A →ₗ[R] B)
    (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)
    (hf : ∀ p, ∀ x ∈ F p, f x ∈ G p) (p : ℕ) (x : F (p + 1)) :
    f.filtrationLayerMap F G hf p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.filtrationStage F G hf (p + 1) x) := rfl

/-- Let R be a ring, e : A →ₗ[R] B and d : B →ₗ[R] C preserve submodule families P,F,H,
respectively. Fix p ∈ ℕ and assume range(e_p^gr)=ker(d_p^gr) for the induced maps on the
adjacent quotients P_{p+1}/(P_p∩P_{p+1}), F_{p+1}/(F_p∩F_{p+1}), and H_{p+1}/(H_p∩H_{p+1}). If
z ∈ F_{p+1} and d(z)=0, then there is y ∈ P_{p+1} with z−e(y) ∈ F_p. Thus a quotient boundary
has a representative whose error is one stage lower. -/
theorem exists_boundary_mod_filtration
    (e : A →ₗ[R] B) (d : B →ₗ[R] C)
    (P : ℕ → Submodule R A) (F : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (he : ∀ p, ∀ x ∈ P p, e x ∈ F p)
    (hd : ∀ p, ∀ x ∈ F p, d x ∈ H p)
    (p : ℕ)
    (hgr : LinearMap.range (e.filtrationLayerMap P F he p) =
      LinearMap.ker (d.filtrationLayerMap F H hd p))
    (z : B) (hzF : z ∈ F (p + 1)) (hz : d z = 0) :
    ∃ y : A, y ∈ P (p + 1) ∧ z - e y ∈ F p := by
  let zF : F (p + 1) := ⟨z, hzF⟩
  let qz : Submodule.FiltrationLayer F p := (Submodule.filtrationLower F p).mkQ zF
  have hqz : d.filtrationLayerMap F H hd p qz = 0 := by
    change d.filtrationLayerMap F H hd p (Submodule.Quotient.mk zF) = 0
    rw [filtrationLayerMap_mkQ]
    have hdz : d.filtrationStage F H hd (p + 1) zF = 0 := by
      apply Subtype.ext
      exact hz
    rw [hdz]
    rfl
  have hrange : qz ∈ LinearMap.range (e.filtrationLayerMap P F he p) := by
    rw [hgr, LinearMap.mem_ker]
    exact hqz
  obtain ⟨qy, hqy⟩ := hrange
  obtain ⟨yP, rfl⟩ := Submodule.mkQ_surjective (Submodule.filtrationLower P p) qy
  refine ⟨yP.val, yP.property, ?_⟩
  have hzero : (Submodule.filtrationLower F p).mkQ
      (zF - e.filtrationStage P F he (p + 1) yP) = 0 := by
    rw [map_sub]
    change qz - e.filtrationLayerMap P F he p
      ((Submodule.filtrationLower P p).mkQ yP) = 0
    rw [hqy, sub_self]
  have hlower := (Submodule.Quotient.mk_eq_zero
    (Submodule.filtrationLower F p)).mp hzero
  exact hlower

/-- Let R be a ring and e : A →ₗ[R] B, d : B →ₗ[R] C preserve submodule families P_p,F_p,H_p.
Assume d∘e=0, F_0=0, every z ∈ B belongs to some F_p, and for every p the induced adjacent
quotient maps satisfy range(e_p^gr)=ker(d_p^gr). Then range(e)=ker(d). The quotient
denominators are the intersections of adjacent stages inside the upper stages. No monotonicity
of the families or exhaustiveness of P and H is assumed, and A,B,C may have independent
carrier universes. -/
theorem range_eq_ker_of_exact_filtrationLayers
    (e : A →ₗ[R] B) (d : B →ₗ[R] C)
    (P : ℕ → Submodule R A) (F : ℕ → Submodule R B) (H : ℕ → Submodule R C)
    (he : ∀ p, ∀ x ∈ P p, e x ∈ F p)
    (hd : ∀ p, ∀ x ∈ F p, d x ∈ H p)
    (hde : d.comp e = 0)
    (hzero : F 0 = ⊥)
    (hexhaustive : ∀ z : B, ∃ p : ℕ, z ∈ F p)
    (hgr : ∀ p, LinearMap.range (e.filtrationLayerMap P F he p) =
      LinearMap.ker (d.filtrationLayerMap F H hd p)) :
    LinearMap.range e = LinearMap.ker d := by
  have hde_apply (y : A) : d (e y) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun hde y
  have hfinite (p : ℕ) :
      ∀ z : B, z ∈ F p → d z = 0 → ∃ y : A, e y = z := by
    induction p with
    | zero =>
        intro z hz hdz
        rw [hzero, Submodule.mem_bot] at hz
        subst z
        exact ⟨0, e.map_zero⟩
    | succ p ih =>
        intro z hz hdz
        obtain ⟨y, _, hlower⟩ :=
          exists_boundary_mod_filtration e d P F H he hd p (hgr p) z hz hdz
        have hcycle : d (z - e y) = 0 := by
          rw [map_sub, hdz, hde_apply, sub_self]
        obtain ⟨y₀, hy₀⟩ := ih (z - e y) hlower hcycle
        refine ⟨y₀ + y, ?_⟩
        rw [map_add, hy₀, sub_add_cancel]
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    exact hde_apply y
  · intro z hz
    obtain ⟨p, hp⟩ := hexhaustive z
    exact hfinite p z hp hz

end LinearMap
