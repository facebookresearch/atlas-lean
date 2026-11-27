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

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.Order.DirectedInverseSystem

/-!
# Diagonal tensor direct limits and mixed-stage tensors

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The R-linear equivalence Lδ≃LM⊗_RLN sends d_a(x⊗y) to m_a(x)⊗n_a(y), with inverse S_ab on
mixed-stage classes. No injective-transition assumption is used.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe r i m n

namespace TensorProduct

variable {R : Type r} [CommSemiring R] {ι : Type i} [Preorder ι] [DecidableEq ι]
  {M : ι → Type m} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
  {N : ι → Type n} [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]
  (f : ∀ a b, a ≤ b → M a →ₗ[R] M b)
  (g : ∀ a b, a ≤ b → N a →ₗ[R] N b)

/-- **Simultaneous tensor transition map.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. The map diagonalTransition f g a b h is δ_ab=f_ab⊗g_ab.
-/
def diagonalTransition (a b : ι) (h : a ≤ b) :
    M a ⊗[R] N a →ₗ[R] M b ⊗[R] N b :=
  TensorProduct.map (f a b h) (g a b h)

/-- **Module direct limit of simultaneous tensor stages.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. The module diagonalLimit f g is Lδ, represented by stage tensors with
transition relations z_a∼δ_ab(z)_b.
-/
abbrev diagonalLimit :=
  Module.DirectLimit (fun j => M j ⊗[R] N j) (diagonalTransition f g)

/-- **Mixed tensor represented at a specified upper stage.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. For a,b≤c, diagonalStageAt a b c sends z∈M_a⊗N_b to d_c((f_ac⊗g_bc)z).
-/
def diagonalStageAt (a b c : ι) (ha : a ≤ c) (hb : b ≤ c) :
    M a ⊗[R] N b →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
    (diagonalTransition f g) c).comp (TensorProduct.map (f a c ha) (g b c hb))

@[simp]
theorem diagonalStageAt_tmul (a b c : ι) (ha : a ≤ c) (hb : b ≤ c)
    (x : M a) (y : N b) :
    diagonalStageAt f g a b c ha hb (x ⊗ₜ[R] y) =
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
        (diagonalTransition f g) c (f a c ha x ⊗ₜ[R] g b c hb y) := by
  simp only [diagonalStageAt, LinearMap.comp_apply, TensorProduct.map_tmul]

variable [DirectedSystem M (f · · ·)] [DirectedSystem N (g · · ·)]

omit [DecidableEq ι] in
/-- **Tensor transitions satisfy the directed-system laws.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. The
simultaneous transitions δ satisfy δ_aa=id and δ_bc∘δ_ab=δ_ac for a≤b≤c.
-/
instance diagonalDirectedSystem :
    DirectedSystem (fun a => M a ⊗[R] N a) (diagonalTransition f g · · ·) where
  map_self a z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [diagonalTransition, TensorProduct.map_tmul,
          DirectedSystem.map_self' f, DirectedSystem.map_self' g]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_map {c b a} hab hbc z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [diagonalTransition, TensorProduct.map_tmul,
          DirectedSystem.map_map' f hab hbc, DirectedSystem.map_map' g hab hbc]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- **Raising the common tensor stage preserves its limit class.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. For
a,b≤c≤d, d_c((f_ac⊗g_bc)z)=d_d((f_ad⊗g_bd)z), so diagonalStageAt is unchanged by raising c to
d.
-/
theorem diagonalStageAt_mono (a b c d : ι) (ha : a ≤ c) (hb : b ≤ c)
    (h : c ≤ d) :
    diagonalStageAt f g a b c ha hb =
      diagonalStageAt f g a b d (ha.trans h) (hb.trans h) := by
  apply TensorProduct.ext'
  intro x y
  rw [diagonalStageAt_tmul, diagonalStageAt_tmul]
  have he := Module.DirectLimit.of_f
    (R := R) (ι := ι) (G := fun j => M j ⊗[R] N j)
    (f := diagonalTransition f g) (i := c) (j := d) (hij := h)
    (x := f a c ha x ⊗ₜ[R] g b c hb y)
  simp only [diagonalTransition, TensorProduct.map_tmul,
    DirectedSystem.map_map' f, DirectedSystem.map_map' g] at he
  exact he.symm

variable [IsDirectedOrder ι]

/-- **Independence of a chosen common tensor upper stage.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c. If
both c,d bound a,b from above, the maps diagonalStageAt a b c and diagonalStageAt a b d
coincide.
-/
theorem diagonalStageAt_eq (a b c d : ι) (ha : a ≤ c) (hb : b ≤ c)
    (ha' : a ≤ d) (hb' : b ≤ d) :
    diagonalStageAt f g a b c ha hb = diagonalStageAt f g a b d ha' hb' := by
  obtain ⟨e, hc, hd⟩ := exists_ge_ge c d
  exact (diagonalStageAt_mono f g a b c e ha hb hc).trans
    (diagonalStageAt_mono f g a b d e ha' hb' hd).symm


/-- **Canonical mixed-stage tensor map into the diagonal limit.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The map diagonalStage a b:M_a⊗N_b→Lδ is S_ab, represented at any common upper stage.
-/
def diagonalStage (a b : ι) : M a ⊗[R] N b →ₗ[R] diagonalLimit f g :=
  let h := exists_ge_ge a b
  diagonalStageAt f g a b (Classical.choose h)
    (Classical.choose_spec h).1 (Classical.choose_spec h).2

theorem diagonalStage_eq (a b c : ι) (ha : a ≤ c) (hb : b ≤ c) :
    diagonalStage f g a b = diagonalStageAt f g a b c ha hb := by
  let h := exists_ge_ge a b
  exact diagonalStageAt_eq f g a b (Classical.choose h) c
    (Classical.choose_spec h).1 (Classical.choose_spec h).2 ha hb

/-- **Mixed-stage map respects the second factor transition.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For b≤c, S_ac∘(id_(M_a)⊗g_bc)=S_ab.
-/
theorem diagonalStage_comp_right (a b c : ι) (h : b ≤ c) :
    (diagonalStage f g a c).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (g b c h)) =
      diagonalStage f g a b := by
  obtain ⟨d, ha, hc⟩ := exists_ge_ge a c
  rw [diagonalStage_eq f g a c d ha hc, diagonalStage_eq f g a b d ha (h.trans hc)]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    diagonalStageAt_tmul, DirectedSystem.map_map' g]

/-- **Mixed-stage map respects the first factor transition.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For a≤c, S_cb∘(f_ac⊗id_(N_b))=S_ab.
-/
theorem diagonalStage_comp_left (a b c : ι) (h : a ≤ c) :
    (diagonalStage f g c b).comp
        (TensorProduct.map (f a c h) (LinearMap.id : N b →ₗ[R] N b)) =
      diagonalStage f g a b := by
  obtain ⟨d, hc, hb⟩ := exists_ge_ge c b
  rw [diagonalStage_eq f g c b d hc hb, diagonalStage_eq f g a b d (h.trans hc) hb]
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    diagonalStageAt_tmul, DirectedSystem.map_map' f]

/-- **Diagonal mixed-stage map is the canonical stage inclusion.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For a∈I, S_aa=d_a:M_a⊗N_a→Lδ.
-/
theorem diagonalStage_self (a : ι) :
    diagonalStage f g a a =
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j) (diagonalTransition f g) a := by
  rw [diagonalStage_eq f g a a a le_rfl le_rfl]
  apply TensorProduct.ext'
  intro x y
  simp only [diagonalStageAt_tmul, DirectedSystem.map_self' f, DirectedSystem.map_self' g]


omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
/-- **Forward comparison to the tensor of module limits.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. The R-linear map diagonalToTensor:Lδ→LM⊗LN sends d_a(z) to (m_a⊗n_a)(z).
This formula requires no directed-order or transition-law assumption.
-/
def diagonalToTensor :
    diagonalLimit f g →ₗ[R] Module.DirectLimit M f ⊗[R] Module.DirectLimit N g :=
  Module.DirectLimit.lift R ι (fun j => M j ⊗[R] N j) (diagonalTransition f g)
    (fun j => TensorProduct.map (Module.DirectLimit.of R ι M f j)
      (Module.DirectLimit.of R ι N g j)) (by
      intro a b h z
      have he :
          (TensorProduct.map (Module.DirectLimit.of R ι M f b)
              (Module.DirectLimit.of R ι N g b)).comp (diagonalTransition f g a b h) =
            TensorProduct.map (Module.DirectLimit.of R ι M f a)
              (Module.DirectLimit.of R ι N g a) := by
        apply TensorProduct.ext'
        intro x y
        simp only [LinearMap.comp_apply, diagonalTransition, TensorProduct.map_tmul,
          Module.DirectLimit.of_f]
      exact LinearMap.congr_fun he z)

omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
/-- **Forward comparison on a full stage tensor.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. For a∈I and z∈M_a⊗N_a, diagonalToTensor(d_a(z))=(m_a⊗n_a)(z).
-/
@[simp]
theorem diagonalToTensor_of (a : ι) (z : M a ⊗[R] N a) :
    diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a z) =
      TensorProduct.map (Module.DirectLimit.of R ι M f a)
        (Module.DirectLimit.of R ι N g a) z := by
  simp only [diagonalToTensor, Module.DirectLimit.lift_of]

omit [IsDirectedOrder ι] [DirectedSystem M (f · · ·)]
  [DirectedSystem N (g · · ·)] in
theorem diagonalToTensor_of_tmul (a : ι) (x : M a) (y : N a) :
    diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g a y := by
  rw [diagonalToTensor_of, TensorProduct.map_tmul]

/-- **Second-factor limit map with one stage fixed.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For a∈I, diagonalSecond a:M_a⊗LN→Lδ sends x⊗n_b(y) to S_ab(x⊗y).
-/
def diagonalSecond (a : ι) :
    M a ⊗[R] Module.DirectLimit N g →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.lift R ι (fun b => M a ⊗[R] N b)
    (fun b c h => LinearMap.lTensor (M a) (g b c h))
    (fun b => diagonalStage f g a b) (by
      intro b c h z
      exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)).comp
    (TensorProduct.directLimitRight g (M a)).toLinearMap

@[simp]
theorem diagonalSecond_tmul_of (a b : ι) (x : M a) (y : N b) :
    diagonalSecond f g a (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
  let p : Module.DirectLimit (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h)) →ₗ[R] diagonalLimit f g :=
    Module.DirectLimit.lift R ι (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h))
      (fun b => diagonalStage f g a b) (by
        intro b c h z
        exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)
  change p (TensorProduct.directLimitRight g (M a)
    (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) = _
  have he := TensorProduct.directLimitRight_tmul_of (f := g) (M := M a) (i := b) x y
  have hp : p (Module.DirectLimit.of R ι (fun b => M a ⊗[R] N b)
      (fun b c h => LinearMap.lTensor (M a) (g b c h)) b (x ⊗ₜ[R] y)) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
    exact Module.DirectLimit.lift_of (R := R) (ι := ι)
      (G := fun b => M a ⊗[R] N b)
      (f := fun b c h => LinearMap.lTensor (M a) (g b c h))
      (fun b => diagonalStage f g a b) (by
        intro b c h z
        exact LinearMap.congr_fun (diagonalStage_comp_right f g a b c h) z)
      (i := b) (x ⊗ₜ[R] y)
  exact (congrArg p he).trans hp

/-- **Fixed-stage second-factor lift respects a first-factor transition.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For a≤c, diagonalSecond c∘(f_ac⊗id_(LN))=diagonalSecond a.
-/
theorem diagonalSecond_comp (a c : ι) (h : a ≤ c) :
    (diagonalSecond f g c).comp (LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) =
      diagonalSecond f g a := by
  apply TensorProduct.ext'
  intro x z
  have hx :
      TensorProduct.curry
          ((diagonalSecond f g c).comp
            (LinearMap.rTensor (Module.DirectLimit N g) (f a c h))) x =
        TensorProduct.curry (diagonalSecond f g a) x := by
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := N) (f := g)
    intro b
    apply LinearMap.ext
    intro y
    change diagonalSecond f g c
        (f a c h x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalSecond f g a (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)
    rw [diagonalSecond_tmul_of, diagonalSecond_tmul_of]
    exact LinearMap.congr_fun (diagonalStage_comp_left f g a b c h) (x ⊗ₜ[R] y)
  exact LinearMap.congr_fun hx z

/-- **Inverse comparison from the tensor of module limits.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The R-linear map tensorToDiagonal:LM⊗LN→Lδ sends m_a(x)⊗n_b(y) to S_ab(x⊗y).
-/
def tensorToDiagonal :
    Module.DirectLimit M f ⊗[R] Module.DirectLimit N g →ₗ[R] diagonalLimit f g :=
  (Module.DirectLimit.lift R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
    (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h))
    (fun a => diagonalSecond f g a) (by
      intro a c h z
      exact LinearMap.congr_fun (diagonalSecond_comp f g a c h) z)).comp
    (TensorProduct.directLimitLeft f (Module.DirectLimit N g)).toLinearMap

/-- **Inverse comparison on a mixed-stage pure tensor.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For x∈M_a,y∈N_b, tensorToDiagonal(m_a(x)⊗n_b(y))=S_ab(x⊗y).
-/
@[simp]
theorem tensorToDiagonal_of_tmul_of (a b : ι) (x : M a) (y : N b) :
    tensorToDiagonal f g
        (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
  let p : Module.DirectLimit (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) →ₗ[R]
        diagonalLimit f g :=
    Module.DirectLimit.lift R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h))
      (fun a => diagonalSecond f g a) (by
        intro a c h z
        exact LinearMap.congr_fun (diagonalSecond_comp f g a c h) z)
  change p (TensorProduct.directLimitLeft f (Module.DirectLimit N g)
    (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) = _
  have he := TensorProduct.directLimitLeft_tmul_of (f := f)
    (M := Module.DirectLimit N g) (i := a) x (Module.DirectLimit.of R ι N g b y)
  have hp : p (Module.DirectLimit.of R ι (fun a => M a ⊗[R] Module.DirectLimit N g)
      (fun a c h => LinearMap.rTensor (Module.DirectLimit N g) (f a c h)) a
        (x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y)) =
      diagonalStage f g a b (x ⊗ₜ[R] y) := by
    simp only [p, Module.DirectLimit.lift_of, diagonalSecond_tmul_of]
  exact (congrArg p he).trans hp


/-- **Forward comparison of a mixed-stage diagonal class.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For x∈M_a,y∈N_b, diagonalToTensor(S_ab(x⊗y))=m_a(x)⊗n_b(y).
-/
theorem diagonalToTensor_diagonalStage (a b : ι) (x : M a) (y : N b) :
    diagonalToTensor f g (diagonalStage f g a b (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y := by
  obtain ⟨c, ha, hb⟩ := exists_ge_ge a b
  rw [diagonalStage_eq f g a b c ha hb, diagonalStageAt_tmul,
    diagonalToTensor_of_tmul, Module.DirectLimit.of_f, Module.DirectLimit.of_f]

/-- **Forward then inverse tensor comparison identity.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The maps Ψ=diagonalToTensor and Φ=tensorToDiagonal satisfy Ψ∘Φ=id_(LM⊗LN).
-/
theorem diagonalToTensor_comp_tensorToDiagonal :
    (diagonalToTensor f g).comp (tensorToDiagonal f g) = LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  have he :
      TensorProduct.curry ((diagonalToTensor f g).comp (tensorToDiagonal f g)) =
        TensorProduct.curry
          (LinearMap.id : Module.DirectLimit M f ⊗[R] Module.DirectLimit N g →ₗ[R]
            Module.DirectLimit M f ⊗[R] Module.DirectLimit N g) := by
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := M) (f := f)
    intro a
    apply LinearMap.ext
    intro u
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι) (G := N) (f := g)
    intro b
    apply LinearMap.ext
    intro v
    change diagonalToTensor f g
        (tensorToDiagonal f g
          (Module.DirectLimit.of R ι M f a u ⊗ₜ[R] Module.DirectLimit.of R ι N g b v)) =
      Module.DirectLimit.of R ι M f a u ⊗ₜ[R] Module.DirectLimit.of R ι N g b v
    rw [tensorToDiagonal_of_tmul_of, diagonalToTensor_diagonalStage]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- **Inverse then forward diagonal comparison identity.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The maps Ψ=diagonalToTensor and Φ=tensorToDiagonal satisfy Φ∘Ψ=id_(Lδ).
-/
theorem tensorToDiagonal_comp_diagonalToTensor :
    (tensorToDiagonal f g).comp (diagonalToTensor f g) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext (R := R) (ι := ι)
    (G := fun j => M j ⊗[R] N j) (f := diagonalTransition f g)
  intro a
  apply TensorProduct.ext'
  intro x y
  change tensorToDiagonal f g
      (diagonalToTensor f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y))) =
    Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
      (diagonalTransition f g) a (x ⊗ₜ[R] y)
  rw [diagonalToTensor_of_tmul, tensorToDiagonal_of_tmul_of, diagonalStage_self]

/-- **Tensor product commutes with the diagonal module limit.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
The R-linear equivalence directLimitDiagonal:Lδ≃ₗ[R]LM⊗LN has forward map diagonalToTensor and
inverse tensorToDiagonal.
-/
def directLimitDiagonal :
    diagonalLimit f g ≃ₗ[R] Module.DirectLimit M f ⊗[R] Module.DirectLimit N g :=
  LinearEquiv.ofLinearMap (diagonalToTensor f g) (tensorToDiagonal f g)
    (diagonalToTensor_comp_tensorToDiagonal f g)
    (tensorToDiagonal_comp_diagonalToTensor f g)

/-- **Diagonal tensor equivalence on an arbitrary stage tensor.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For z∈M_a⊗N_a, directLimitDiagonal(d_a(z))=(m_a⊗n_a)(z).
-/
@[simp]
theorem directLimitDiagonal_of (a : ι) (z : M a ⊗[R] N a) :
    directLimitDiagonal f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a z) =
      TensorProduct.map (Module.DirectLimit.of R ι M f a)
        (Module.DirectLimit.of R ι N g a) z := by
  exact diagonalToTensor_of f g a z

/-- **Diagonal tensor equivalence on a stage pure tensor.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For x∈M_a,y∈N_a, directLimitDiagonal(d_a(x⊗y))=m_a(x)⊗n_a(y).
-/
theorem directLimitDiagonal_of_tmul (a : ι) (x : M a) (y : N a) :
    directLimitDiagonal f g
        (Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
          (diagonalTransition f g) a (x ⊗ₜ[R] y)) =
      Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g a y :=
  diagonalToTensor_of_tmul f g a x y

/-- **Inverse tensor equivalence on two stage classes.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c.
For x∈M_a,y∈N_b, directLimitDiagonal⁻¹(m_a(x)⊗n_b(y))=S_ab(x⊗y).
-/
@[simp]
theorem directLimitDiagonal_symm_of_tmul_of (a b : ι) (x : M a) (y : N b) :
    (directLimitDiagonal f g).symm
        (Module.DirectLimit.of R ι M f a x ⊗ₜ[R] Module.DirectLimit.of R ι N g b y) =
      diagonalStage f g a b (x ⊗ₜ[R] y) :=
  tensorToDiagonal_of_tmul_of f g a b x y

/-- **A tensor class vanishing in the limits vanishes at a later stage.**

Let R be a commutative semiring, I a preorder, M_i,N_i R-semimodules and
f_ab:M_a→M_b,g_ab:N_a→N_b transition families for a≤b. Write δ_ab=f_ab⊗g_ab, Lδ for the
presented module direct limit of M_i⊗_RN_i, and LM,LN for the two factor limits with stage
maps m_a,n_a,d_a. Assume f,g satisfy the directed-system identity and composition laws. Assume
I is upward directed. For a,b≤c, put S_ab(z)=d_c((f_ac⊗g_bc)(z)); this is independent of c. If
z∈M_a⊗N_a satisfies (m_a⊗n_a)(z)=0, then there exist c≥a with (f_ac⊗g_ac)(z)=0.
-/
theorem exists_eq_zero_of_map_to_directLimit_diagonal_eq_zero
    {a : ι} (z : M a ⊗[R] N a)
    (hz : TensorProduct.map (Module.DirectLimit.of R ι M f a)
      (Module.DirectLimit.of R ι N g a) z = 0) :
    ∃ c : ι, ∃ h : a ≤ c,
      TensorProduct.map (f a c h) (g a c h) z = 0 := by
  have hcolimit :
      Module.DirectLimit.of R ι (fun j => M j ⊗[R] N j)
        (diagonalTransition f g) a z = 0 := by
    apply (directLimitDiagonal f g).injective
    rw [directLimitDiagonal_of, map_zero]
    exact hz
  exact Module.DirectLimit.of.zero_exact hcolimit

end TensorProduct
