/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Coefficients
public import MathlibExt.Algebra.Homology.Hochschild.Basic
public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.Homotopy
public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.SimplicialComparison
public import Mathlib.Algebra.Algebra.Tower

/-!
# Hochschild chains with nonunital coefficient actions

Let k be a commutative ring and A a nonunital associative ring with
k-bilinear multiplication. Let M be a k-module with commuting
nonunital representations l : A → End_k(M) and
r : Aᵐᵒᵖ → End_k(M). The coefficient chain term is
C_n(A,M) = M ⊗[k] A^{⊗n}.

The first face uses r(op a_1)m, the interior faces multiply consecutive
algebra factors, and the last face uses l(a_{n+1})m. The resulting
semisimplicial object has alternating boundary
b_{n+1} = ∑_{i=0}^{n+1} (−1)^i δ_i; in degree one,
b_1(m ⊗ a) = r(op a)m − l(a)m under C_0 ≃ M.

Unitization extends the two actions to U(A) = k ⊕ A. The inclusion
of every A-factor into U(A) is split by its k-linear second-coordinate
projection. The ambient Hochschild faces preserve the included tensor
submodules, giving the nonunital semisimplicial faces above.
All coefficient tensor terms lie in ModuleCat over k at max{u,v,w}.

Reference: J.-L. Loday, Cyclic Homology, §1.1.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k]
  {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
A nonunital left representation l : A → End_k(M) gives the
U(A)-module structure (λ,a)m = λm + l(a)m. -/
abbrev leftModule (l : A →ₙₐ[k] Module.End k M) : Module (Unitization k A) M :=
  Module.compHom M (unitizationLeft l).toRingHom

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
A nonunital right representation r : Aᵐᵒᵖ → End_k(M) gives
the U(A)ᵐᵒᵖ-module structure op(λ,a) • m = λm + r(op a)m. -/
abbrev rightModule (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) :
    Module (Unitization k A)ᵐᵒᵖ M :=
  Module.compHom M (unitizationRight r).toRingHom

theorem leftGroundComm (l : A →ₙₐ[k] Module.End k M) :
    letI := leftModule l
    SMulCommClass k (Unitization k A) M := by
  let := leftModule l
  exact ⟨fun c a m => (unitizationLeft l a).map_smul c m |>.symm⟩

theorem rightGroundComm (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) :
    letI := rightModule r
    SMulCommClass k (Unitization k A)ᵐᵒᵖ M := by
  let := rightModule r
  exact ⟨fun c a m => (unitizationRight r a).map_smul c m |>.symm⟩

theorem leftTower (l : A →ₙₐ[k] Module.End k M) :
    letI := leftModule l
    IsScalarTower k (Unitization k A) M := by
  let := leftModule l
  refine ⟨fun c a m => ?_⟩
  change unitizationLeft l (c • a) m = c • unitizationLeft l a m
  rw [map_smul]
  rfl

theorem rightTower (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) :
    letI := rightModule r
    IsScalarTower k (Unitization k A)ᵐᵒᵖ M := by
  let := rightModule r
  refine ⟨fun c a m => ?_⟩
  change unitizationRight r (c • a) m = c • unitizationRight r a m
  rw [map_smul]
  rfl

theorem actionsComm (l : A →ₙₐ[k] Module.End k M)
    (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
    (h : ∀ a b m, l a (r b m) = r b (l a m)) :
    letI := leftModule l
    letI := rightModule r
    SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ M := by
  let := leftModule l
  let := rightModule r
  exact ⟨unitization_commute l r h⟩

/-- Let k : Type u be commutative, A : Type v a nonunital associative
ring with a k-module structure, and M : Type w a k-module.
The degree-n coefficient tensor object is M ⊗[k] A^{⊗n},
viewed in ModuleCat over k at universe max{u,v,w}. -/
abbrev chainLevel (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A]
    [Module k A] (M : Type w) [AddCommGroup M] [Module k M] (n : ℕ) :
    ModuleCat.{max u v w} k :=
  ModuleCat.of k (M ⊗[k] TensorPower k n A)

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
The unitized coefficient tensor object in degree n is
M ⊗[k] U(A)^{⊗n}, in the common module category over k. -/
abbrev unitizedLevel (n : ℕ) : ModuleCat.{max u v w} k :=
  ModuleCat.of k (M ⊗[k] TensorPower k n (Unitization k A))

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
The inclusion C_n(A,M) → C_n(U(A),M) fixes M and sends each
algebra factor a to (0,a) ∈ U(A). It is a k-linear map. -/
def inclusion (n : ℕ) : chainLevel k A M n ⟶ unitizedLevel (k := k) (A := A) (M := M) n :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id
    (PiTensorProduct.map (fun _ : Fin n => Unitization.inrHom k k A)))

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
The k-linear map C_n(U(A),M) → C_n(A,M) fixes M and applies
p(λ,a) = a to every algebra factor. It is a retraction of the
factorwise inclusion a ↦ (0,a). -/
def retraction (n : ℕ) : unitizedLevel (k := k) (A := A) (M := M) n ⟶ chainLevel k A M n :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id
    (PiTensorProduct.map (fun _ : Fin n => Unitization.sndHom k k A)))

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem inclusion_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    (inclusion (k := k) (A := A) (M := M) n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => Unitization.inr (a i)) := by
  simp only [inclusion, ModuleCat.hom_ofHom, TensorProduct.map_tmul,
    LinearMap.id_apply, PiTensorProduct.map_tprod, Unitization.inrHom_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem retraction_tprod (n : ℕ) (m : M) (a : Fin n → Unitization k A) :
    (retraction (k := k) (A := A) (M := M) n).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => (a i).snd) := by
  simp only [retraction, ModuleCat.hom_ofHom, TensorProduct.map_tmul,
    LinearMap.id_apply, PiTensorProduct.map_tprod, Unitization.sndHom_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem inclusion_retraction (n : ℕ) :
    inclusion (k := k) (A := A) (M := M) n ≫ retraction n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply]
  rw [inclusion_tprod, retraction_tprod]
  rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
private theorem inclusion_injective (n : ℕ) :
    Function.Injective (inclusion (k := k) (A := A) (M := M) n).hom := by
  apply Function.LeftInverse.injective (g := (retraction n).hom)
  intro x
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (inclusion_retraction (k := k) (A := A) (M := M) n)) x

section Bar

variable (l : A →ₙₐ[k] Module.End k M)
  (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
  (h : ∀ a b m, l a (r b m) = r b (l a m))

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
The extended U(A)-bimodule M gives the ambient coefficient
Hochschild semisimplicial object with degree-n term
M ⊗[k] U(A)^{⊗n}. -/
@[implicit_reducible]
def ambient : SemiSimplicialObject (ModuleCat.{max u v w} k) := by
  letI := Module.compHom M (unitizationLeft l).toRingHom
  letI := Module.compHom M (unitizationRight r).toRingHom
  letI := leftGroundComm l
  letI := rightGroundComm r
  letI := leftTower l
  letI := rightTower r
  letI := actionsComm l r h
  let S := SemiSimplexCategory.toSimplexCategory.op ⋙
    ModuleCat.Algebra.Hochschild.coefficientBar k (Unitization k A) M
  let e (a : SemiSimplexCategoryᵒᵖ) : S.obj a ≅ unitizedLevel a.unop.len :=
    ModuleCat.Algebra.Hochschild.coefficientBarObjIso k (Unitization k A) M a.unop.len
  exact
    { obj a := unitizedLevel a.unop.len
      map {a b} f := (e a).inv ≫ S.map f ≫ (e b).hom
      map_id a := by
        rw [S.map_id, Category.id_comp]
        exact (e a).inv_hom_id
      map_comp f g := by
        simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] }

private theorem ambient_face_first (n : ℕ) (m : M) (a : Fin (n + 1) → Unitization k A) :
    ((ambient l r h).δ (0 : Fin (n + 2))).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      unitizationRight r (MulOpposite.op (a 0)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a) := by
  let := leftModule l
  let := rightModule r
  let := leftGroundComm l
  let := rightGroundComm r
  let := leftTower l
  let := rightTower r
  let := actionsComm l r h
  change (ModuleCat.Algebra.Hochschild.face k (Unitization k A) M n 0).hom
    (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  exact ModuleCat.Algebra.Hochschild.face_first_tprod k (Unitization k A) M n m a

private theorem ambient_face_inner (n : ℕ) (i : Fin n) (m : M)
    (a : Fin (n + 1) → Unitization k A) :
    ((ambient l r h).δ i.castSucc.succ).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a) := by
  let := leftModule l
  let := rightModule r
  let := leftGroundComm l
  let := rightGroundComm r
  let := leftTower l
  let := rightTower r
  let := actionsComm l r h
  change (ModuleCat.Algebra.Hochschild.face k (Unitization k A) M n i.castSucc.succ).hom
    (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  exact ModuleCat.Algebra.Hochschild.face_inner_tprod k (Unitization k A) M n i m a

private theorem ambient_face_last (n : ℕ) (m : M) (a : Fin (n + 1) → Unitization k A) :
    ((ambient l r h).δ (Fin.last (n + 1))).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      unitizationLeft l (a (Fin.last n)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropLast a) := by
  let := leftModule l
  let := rightModule r
  let := leftGroundComm l
  let := rightGroundComm r
  let := leftTower l
  let := rightTower r
  let := actionsComm l r h
  change (ModuleCat.Algebra.Hochschild.face k (Unitization k A) M n (Fin.last (n + 1))).hom
    (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  exact ModuleCat.Algebra.Hochschild.face_last_tprod k (Unitization k A) M n m a

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
The face δ_i : C_{n+1}(A,M) → C_n(A,M) is the restriction of
the corresponding unitized face to the included tensor submodule.
Its first face uses r(op a_1)m, its interior faces merge a_i a_{i+1},
and its last face uses l(a_{n+1})m. -/
@[implicit_reducible]
def face (n : ℕ) (i : Fin (n + 2)) : chainLevel k A M (n + 1) ⟶ chainLevel k A M n :=
  inclusion (n + 1) ≫ (ambient l r h).δ i ≫ retraction n

@[simp]
theorem face_first_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    (face l r h n 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      r (MulOpposite.op (a 0)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropFirst a) := by
  simp only [face, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [inclusion_tprod, ambient_face_first]
  rw [unitizationRight_inr]
  change (retraction n).hom
      (r (MulOpposite.op (a 0)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => Unitization.inr (a i.succ))) = _
  rw [retraction_tprod]
  rfl

@[simp]
theorem face_inner_tprod (n : ℕ) (i : Fin n) (m : M) (a : Fin (n + 1) → A) :
    (face l r h n i.castSucc.succ).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a) := by
  simp only [face, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [inclusion_tprod, ambient_face_inner, retraction_tprod]
  congr 2
  funext j
  simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent]
  split_ifs
  · rw [← Unitization.inr_mul, Unitization.snd_inr]
  · rfl

@[simp]
theorem face_last_tprod (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    (face l r h n (Fin.last (n + 1))).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      l (a (Fin.last n)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildDropLast a) := by
  simp only [face, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [inclusion_tprod, ambient_face_last]
  rw [unitizationLeft_inr]
  change (retraction n).hom
      (l (a (Fin.last n)) m ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => Unitization.inr (a i.castSucc))) = _
  rw [retraction_tprod]
  rfl

private theorem inclusion_face (n : ℕ) (i : Fin (n + 2)) :
    face l r h n i ≫ inclusion n = inclusion (n + 1) ≫ (ambient l r h).δ i := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  change (inclusion n).hom ((face l r h n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ((ambient l r h).δ i).hom
      ((inclusion (n + 1)).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun q => ?_) j) i
  · rw [face_first_tprod, inclusion_tprod, inclusion_tprod, ambient_face_first,
      unitizationRight_inr]
    rfl
  · simp only [Fin.succ_last]
    rw [face_last_tprod, inclusion_tprod, inclusion_tprod, ambient_face_last,
      unitizationLeft_inr]
    rfl
  · rw [face_inner_tprod, inclusion_tprod, inclusion_tprod, ambient_face_inner]
    congr 2
    funext j
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent]
    split_ifs <;> simp only [Unitization.inr_mul]

private theorem inclusion_map {a b : SemiSimplexCategory} (f : a ⟶ b) :
    (inclusion b.len ≫ (ambient l r h).map f.op ≫ retraction a.len) ≫ inclusion a.len =
      inclusion b.len ≫ (ambient l r h).map f.op := by
  let P : MorphismProperty SemiSimplexCategory := fun a b f =>
    (inclusion b.len ≫ (ambient l r h).map f.op ≫ retraction a.len) ≫ inclusion a.len =
      inclusion b.len ≫ (ambient l r h).map f.op
  change P f
  apply SemiSimplexCategory.hom_induction
  · intro a
    change (inclusion a.len ≫ (ambient l r h).map (𝟙 (op a)) ≫ retraction a.len) ≫
      inclusion a.len = inclusion a.len ≫ (ambient l r h).map (𝟙 (op a))
    rw [(ambient l r h).map_id]
    change (inclusion a.len ≫ 𝟙 (unitizedLevel a.len) ≫ retraction a.len) ≫
      inclusion a.len = inclusion a.len ≫ 𝟙 (unitizedLevel a.len)
    rw [Category.id_comp, Category.comp_id,
      inclusion_retraction, Category.id_comp]
  · intro a b g i ih
    change (inclusion (b.len + 1) ≫
        (ambient l r h).map (g ≫ SemiSimplexCategory.δ i).op ≫ retraction a.len) ≫
        inclusion a.len =
      inclusion (b.len + 1) ≫ (ambient l r h).map (g ≫ SemiSimplexCategory.δ i).op
    have hg : (inclusion b.len ≫ (ambient l r h).map g.op ≫ retraction a.len) ≫
        inclusion a.len = inclusion b.len ≫ (ambient l r h).map g.op := ih
    have hf := inclusion_face l r h b.len i
    calc
      _ = face l r h b.len i ≫
          ((inclusion b.len ≫ (ambient l r h).map g.op ≫ retraction a.len) ≫
            inclusion a.len) := by
        simpa only [op_comp, Functor.map_comp, SemiSimplicialObject.δ_def,
          Category.assoc] using congrArg
            (fun q => q ≫ (ambient l r h).map g.op ≫ retraction a.len ≫ inclusion a.len)
            hf.symm
      _ = face l r h b.len i ≫
          (inclusion b.len ≫ (ambient l r h).map g.op) := congrArg _ hg
      _ = _ := by
        simpa only [op_comp, Functor.map_comp, SemiSimplicialObject.δ_def,
          Category.assoc] using congrArg (fun q => q ≫ (ambient l r h).map g.op) hf

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
The coefficient tensor terms C_n(A,M) = M ⊗[k] A^{⊗n},
with the endpoint action faces and interior multiplication faces,
form a semisimplicial k-module object. -/
@[implicit_reducible]
def bar : SemiSimplicialObject (ModuleCat.{max u v w} k) where
  obj a := chainLevel k A M a.unop.len
  map {a b} f := inclusion a.unop.len ≫ (ambient l r h).map f ≫ retraction b.unop.len
  map_id a := by
    rw [(ambient l r h).map_id]
    change inclusion a.unop.len ≫ 𝟙 (unitizedLevel a.unop.len) ≫ retraction a.unop.len = _
    rw [Category.id_comp]
    exact inclusion_retraction a.unop.len
  map_comp {a b c} f g := by
    change (inclusion a.unop.len ≫ (ambient l r h).map (f ≫ g) ≫ retraction c.unop.len) =
      (inclusion a.unop.len ≫ (ambient l r h).map f ≫ retraction b.unop.len) ≫
        (inclusion b.unop.len ≫ (ambient l r h).map g ≫ retraction c.unop.len)
    have hf := inclusion_map l r h f.unop
    calc
      _ = (inclusion a.unop.len ≫ (ambient l r h).map f) ≫
          (ambient l r h).map g ≫ retraction c.unop.len := by
        simp only [Functor.map_comp, Category.assoc]
      _ = ((inclusion a.unop.len ≫ (ambient l r h).map f ≫ retraction b.unop.len) ≫
            inclusion b.unop.len) ≫ (ambient l r h).map g ≫ retraction c.unop.len :=
        congrArg (fun q => q ≫ (ambient l r h).map g ≫ retraction c.unop.len) hf.symm
      _ = _ := by simp only [Category.assoc]

@[simp]
theorem bar_obj (n : ℕ) : (bar l r h) _⦋n⦌ₛ = chainLevel k A M n := rfl

@[simp]
theorem bar_δ (n : ℕ) (i : Fin (n + 2)) : (bar l r h).δ i = face l r h n i := rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
For i ≤ j in Fin(n+2), the coefficient faces satisfy
δ_i^(n) δ_{j+1}^(n+1) = δ_j^(n) δ_i^(n+1)
as maps C_{n+2}(A,M) → C_n(A,M). -/
theorem face_comp_face (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    face l r h (n + 1) j.succ ≫ face l r h n i =
      face l r h (n + 1) i.castSucc ≫ face l r h n j :=
  SemiSimplicialObject.δ_comp_δ (bar l r h) hij

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
The semisimplicial coefficient bar defines the Hochschild chain
complex over k with terms C_n(A,M) and differential
b_{n+1} = ∑_{i=0}^{n+1} (−1)^i δ_i. -/
@[implicit_reducible]
def complex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex _).obj (bar l r h)

@[simp]
theorem complex_X (n : ℕ) : (complex l r h).X n = chainLevel k A M n := rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
The degree-(n+1) boundary of the coefficient complex is precisely
the alternating sum ∑_{i=0}^{n+1} (−1)^i δ_i of its n+2 faces. -/
theorem complex_d (n : ℕ) :
    (complex l r h).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • face l r h n i := by
  dsimp only [complex]
  rw [AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex_obj_d]
  rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Let l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M) be nonunital
k-algebra representations with commuting values:
l(a)(r(b)m) = r(b)(l(a)m) for every a ∈ A, b ∈ Aᵐᵒᵖ and m ∈ M.
For m ∈ M and a : Fin 1 → A, the first boundary has value
(r(op a_0)m − l(a_0)m) ⊗ tprod(empty).
Under the empty-tensor identification C_0(A,M) ≃ M this is
r(op a_0)m − l(a_0)m. -/
theorem complex_d_one_tprod (m : M) (a : Fin 1 → A) :
    ((complex l r h).d 1 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      r (MulOpposite.op (a 0)) m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 0 => a 0) -
      l (a 0) m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 0 => a 0) := by
  rw [complex_d, Fin.sum_univ_two]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, Fin.val_zero, pow_zero, Fin.val_one, pow_one,
    one_smul, neg_one_smul]
  change (face l r h 0 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) -
      (face l r h 0 (Fin.last 1)).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [face_first_tprod, face_last_tprod]
  congr 2 <;> apply congrArg (PiTensorProduct.tprod k) <;> funext i <;> exact Fin.elim0 i

end Bar

section Unital

variable {B : Type v} [Ring B] [Algebra k B]
  [Module B M] [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M]
  [SMulCommClass k B M] [SMulCommClass k Bᵐᵒᵖ M]
  [IsScalarTower k B M] [IsScalarTower k Bᵐᵒᵖ M]

/-- Let k be commutative, B an associative unital k-algebra, and M a
compatible B-bimodule with commuting k-linear left and right actions.
Choose l(b)m = bm and r(op b)m = mb. Every nonunital coefficient face
δ_i : M ⊗[k] B^{⊗(n+1)} → M ⊗[k] B^{⊗n}
is exactly the corresponding unital Hochschild face. -/
theorem face_eq_unital (n : ℕ) (i : Fin (n + 2)) :
    let l := (Algebra.lsmul k k M (A := B)).toNonUnitalAlgHom
    let r := (Algebra.lsmul k k M (A := Bᵐᵒᵖ)).toNonUnitalAlgHom
    face l r (fun a b m => smul_comm a b m) n i =
      ModuleCat.Algebra.Hochschild.face k B M n i := by
  dsimp only
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun q => ?_) j) i
  · exact (face_first_tprod
      (l := (Algebra.lsmul k k M (A := B)).toNonUnitalAlgHom)
      (r := (Algebra.lsmul k k M (A := Bᵐᵒᵖ)).toNonUnitalAlgHom)
      (h := fun a b m => smul_comm a b m) n m a).trans
        (ModuleCat.Algebra.Hochschild.face_first_tprod k B M n m a).symm
  · simp only [Fin.succ_last]
    exact (face_last_tprod
      (l := (Algebra.lsmul k k M (A := B)).toNonUnitalAlgHom)
      (r := (Algebra.lsmul k k M (A := Bᵐᵒᵖ)).toNonUnitalAlgHom)
      (h := fun a b m => smul_comm a b m) n m a).trans
        (ModuleCat.Algebra.Hochschild.face_last_tprod k B M n m a).symm
  · exact (face_inner_tprod
      (l := (Algebra.lsmul k k M (A := B)).toNonUnitalAlgHom)
      (r := (Algebra.lsmul k k M (A := Bᵐᵒᵖ)).toNonUnitalAlgHom)
      (h := fun a b m => smul_comm a b m) n q m a).trans
        (ModuleCat.Algebra.Hochschild.face_inner_tprod k B M n q m a).symm

end Unital

end ModuleCat.Algebra.Hochschild.NonUnital
