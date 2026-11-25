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

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import MathlibExt.GroupTheory.CentralExtension
public import MathlibExt.GroupTheory.GroupExtension.Hom

/-!
# Pullbacks of group extensions

Constructs the pullback of a group extension along a group homomorphism, with
explicit projection maps and its universal lifting property. Maps of extensions
induce functorial pullback maps, and centrality is preserved.
-/

@[expose] public section

universe u v w₁ w₂ w₃

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w₁} {H : Type w₂}
  [Group N] [Group E] [Group G] [Group H]

/-- The subgroup of pairs `(e, h)` satisfying `S.rightHom e = f h`. -/
def pullbackSubgroup (S : GroupExtension N E G) (f : H →* G) :
    Subgroup (E × H) where
  carrier := {p | S.rightHom p.1 = f p.2}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Prod.fst_mul, Prod.snd_mul, map_mul, ha, hb]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    simp [map_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [Prod.fst_inv, Prod.snd_inv, map_inv, ha]

@[simp]
theorem mem_pullbackSubgroup {S : GroupExtension N E G} {f : H →* G}
    {p : E × H} : p ∈ S.pullbackSubgroup f ↔ S.rightHom p.1 = f p.2 :=
  Iff.rfl

theorem pullbackSubgroup_eq_eqLocus (S : GroupExtension N E G)
    (f : H →* G) :
    S.pullbackSubgroup f =
      MonoidHom.eqLocus (S.rightHom.comp (MonoidHom.fst E H))
        (f.comp (MonoidHom.snd E H)) := by
  ext p
  have h1 : p ∈ S.pullbackSubgroup f ↔ S.rightHom p.1 = f p.2 := Iff.rfl
  have h2 : p ∈ (S.rightHom.comp (MonoidHom.fst E H)).eqLocus
      (f.comp (MonoidHom.snd E H)) ↔
      (S.rightHom.comp (MonoidHom.fst E H)) p =
        (f.comp (MonoidHom.snd E H)) p := Iff.rfl
  rw [h1, h2]
  rfl

/-- The total group of the extension obtained by pulling `S` back along `f`. -/
abbrev PullbackTotal (S : GroupExtension N E G) (f : H →* G) : Type _ :=
  S.pullbackSubgroup f

/-- The projection from the pullback total group to the original total group
`E`. -/
def pullbackFst (S : GroupExtension N E G) (f : H →* G) :
    PullbackTotal S f →* E where
  toFun p := (p : E × H).1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The projection from the pullback total group to the new quotient group
`H`. -/
def pullbackSnd (S : GroupExtension N E G) (f : H →* G) :
    PullbackTotal S f →* H where
  toFun p := (p : E × H).2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem pullbackFst_coe (S : GroupExtension N E G) (f : H →* G)
    (p : PullbackTotal S f) : pullbackFst S f p = (p : E × H).1 := rfl

@[simp]
theorem pullbackSnd_coe (S : GroupExtension N E G) (f : H →* G)
    (p : PullbackTotal S f) : pullbackSnd S f p = (p : E × H).2 := rfl

@[simp]
theorem pullbackFst_mk (S : GroupExtension N E G) (f : H →* G)
    (e : E) (h : H) (hp : (e, h) ∈ S.pullbackSubgroup f) :
    pullbackFst S f ⟨(e, h), hp⟩ = e := rfl

@[simp]
theorem pullbackSnd_mk (S : GroupExtension N E G) (f : H →* G)
    (e : E) (h : H) (hp : (e, h) ∈ S.pullbackSubgroup f) :
    pullbackSnd S f ⟨(e, h), hp⟩ = h := rfl

@[simp]
theorem pullback_condition (S : GroupExtension N E G) (f : H →* G)
    (p : PullbackTotal S f) :
    S.rightHom (pullbackFst S f p) = f (pullbackSnd S f p) :=
  p.2

theorem pullback_square (S : GroupExtension N E G) (f : H →* G) :
    S.rightHom.comp (pullbackFst S f) = f.comp (pullbackSnd S f) := by
  ext p : 1
  exact p.2

section Lift

variable {K : Type w₃} [Group K]

/-- Lift compatible homomorphisms `e : K →* E` and `h : K →* H` to the
pullback total group, with value `(e k, h k)`. -/
def pullbackLift (S : GroupExtension N E G) {f : H →* G}
    (e : K →* E) (h : K →* H)
    (h_comm : S.rightHom.comp e = f.comp h) :
    K →* PullbackTotal S f where
  toFun k :=
    ⟨(e k, h k), by
      have hk := DFunLike.congr_fun h_comm k
      simp only [MonoidHom.comp_apply] at hk
      exact hk⟩
  map_one' := by
    apply Subtype.ext
    simp [map_one]
  map_mul' x y := by
    apply Subtype.ext
    simp [map_mul]

theorem pullbackFst_comp_pullbackLift (S : GroupExtension N E G)
    {f : H →* G} {e : K →* E} {h : K →* H}
    {h_comm : S.rightHom.comp e = f.comp h} :
    (pullbackFst S f).comp (pullbackLift S e h h_comm) = e := by
  ext k : 1
  rfl

theorem pullbackSnd_comp_pullbackLift (S : GroupExtension N E G)
    {f : H →* G} {e : K →* E} {h : K →* H}
    {h_comm : S.rightHom.comp e = f.comp h} :
    (pullbackSnd S f).comp (pullbackLift S e h h_comm) = h := by
  ext k : 1
  rfl

theorem pullbackHom_ext {S : GroupExtension N E G} {f : H →* G}
    {φ ψ : K →* PullbackTotal S f}
    (h1 : (pullbackFst S f).comp φ = (pullbackFst S f).comp ψ)
    (h2 : (pullbackSnd S f).comp φ = (pullbackSnd S f).comp ψ) :
    φ = ψ := by
  ext k : 1
  have hf := DFunLike.congr_fun h1 k
  have hs := DFunLike.congr_fun h2 k
  simp only [MonoidHom.comp_apply] at hf hs
  apply Subtype.ext
  exact Prod.ext hf hs

theorem pullbackLift_unique {S : GroupExtension N E G} {f : H →* G}
    {φ : K →* PullbackTotal S f} :
    φ = pullbackLift S ((pullbackFst S f).comp φ)
        ((pullbackSnd S f).comp φ)
        (by ext k : 1; exact pullback_condition S f (φ k)) := by
  symm
  apply pullbackHom_ext
  · simp [pullbackFst_comp_pullbackLift]
  · simp [pullbackSnd_comp_pullbackLift]

end Lift

section Map

variable {N' E' G' H' : Type*}
variable [Group N'] [Group E'] [Group G'] [Group H']
variable {S : GroupExtension N E G} {T : GroupExtension N' E' G'}

/-- A morphism of extensions and a compatible map of new quotient groups
induce a map between the corresponding pullback total groups. -/
def pullbackMap (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    PullbackTotal S f →* PullbackTotal T g :=
  pullbackLift T
    (m.totalHom.comp (pullbackFst S f))
    (h.comp (pullbackSnd S f))
    (by
      rw [← MonoidHom.comp_assoc, m.rightHom_comm,
        MonoidHom.comp_assoc, pullback_square S f,
        ← MonoidHom.comp_assoc, h_comm, MonoidHom.comp_assoc])

@[simp]
theorem pullbackFst_comp_pullbackMap
    (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackFst T g).comp (pullbackMap m h h_comm) =
      m.totalHom.comp (pullbackFst S f) :=
  pullbackFst_comp_pullbackLift T

@[simp]
theorem pullbackSnd_comp_pullbackMap
    (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackSnd T g).comp (pullbackMap m h h_comm) =
      h.comp (pullbackSnd S f) :=
  pullbackSnd_comp_pullbackLift T

@[simp]
theorem pullbackFst_pullbackMap
    (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h)
    (p : PullbackTotal S f) :
    pullbackFst T g (pullbackMap m h h_comm p) =
      m.totalHom (pullbackFst S f p) :=
  DFunLike.congr_fun (pullbackFst_comp_pullbackMap m h h_comm) p

@[simp]
theorem pullbackSnd_pullbackMap
    (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h)
    (p : PullbackTotal S f) :
    pullbackSnd T g (pullbackMap m h h_comm p) =
      h (pullbackSnd S f p) :=
  DFunLike.congr_fun (pullbackSnd_comp_pullbackMap m h h_comm) p

/-- The induced pullback map is uniquely determined by its two projections. -/
theorem pullbackMap_unique
    (m : S.Hom T) {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h)
    (k : PullbackTotal S f →* PullbackTotal T g)
    (hfst : (pullbackFst T g).comp k =
      m.totalHom.comp (pullbackFst S f))
    (hsnd : (pullbackSnd T g).comp k =
      h.comp (pullbackSnd S f)) :
    k = pullbackMap m h h_comm := by
  apply pullbackHom_ext hfst
  exact hsnd

/-- Pullback along identity morphisms gives the identity map. -/
@[simp]
theorem pullbackMap_id (S : GroupExtension N E G) (f : H →* G) :
    pullbackMap (Hom.id S) (MonoidHom.id H) (by simp) =
      MonoidHom.id (PullbackTotal S f) := by
  apply pullbackHom_ext
  · simp
  · simp

section Composition

variable {N'' E'' G'' H'' : Type*}
variable [Group N''] [Group E''] [Group G''] [Group H'']
variable {U : GroupExtension N'' E'' G''}

/-- Pullback maps preserve composition of extension and base morphisms. -/
theorem pullbackMap_comp
    (m : S.Hom T) (n : T.Hom U)
    {f : H →* G} {g : H' →* G'} {k : H'' →* G''}
    (h : H →* H') (i : H' →* H'')
    (h_comm : m.quotientHom.comp f = g.comp h)
    (i_comm : n.quotientHom.comp g = k.comp i) :
    pullbackMap (n.comp m) (i.comp h) (by
        calc
          (n.comp m).quotientHom.comp f =
              n.quotientHom.comp (m.quotientHom.comp f) := by
            rw [Hom.comp_quotientHom, MonoidHom.comp_assoc]
          _ = n.quotientHom.comp (g.comp h) := by rw [h_comm]
          _ = (n.quotientHom.comp g).comp h := by
            rw [MonoidHom.comp_assoc]
          _ = (k.comp i).comp h := by rw [i_comm]
          _ = k.comp (i.comp h) := by rw [MonoidHom.comp_assoc]) =
      (pullbackMap n i i_comm).comp (pullbackMap m h h_comm) := by
  apply pullbackHom_ext
  · ext p
    change n.totalHom (m.totalHom (pullbackFst S f p)) =
      pullbackFst U k
        (pullbackMap n i i_comm (pullbackMap m h h_comm p))
    rw [pullbackFst_pullbackMap, pullbackFst_pullbackMap]
  · ext p
    change i (h (pullbackSnd S f p)) =
      pullbackSnd U k
        (pullbackMap n i i_comm (pullbackMap m h h_comm p))
    rw [pullbackSnd_pullbackMap, pullbackSnd_pullbackMap]

end Composition

end Map

section Extension

/-- The pullback kernel inclusion, sending `n` to the pair `(S.inl n, 1)`. -/
def pullbackInl (S : GroupExtension N E G) (f : H →* G) :
    N →* PullbackTotal S f where
  toFun n :=
    ⟨(S.inl n, 1), by simp [S.rightHom_inl, map_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [map_one]
  map_mul' x y := by
    apply Subtype.ext
    simp [map_mul]

@[simp]
theorem pullbackInl_coe (S : GroupExtension N E G) (f : H →* G) (n : N) :
    (pullbackInl S f n : E × H) = (S.inl n, 1) := rfl

@[simp]
theorem pullbackFst_pullbackInl (S : GroupExtension N E G) (f : H →* G) (n : N) :
    pullbackFst S f (pullbackInl S f n) = S.inl n := rfl

@[simp]
theorem pullbackSnd_pullbackInl (S : GroupExtension N E G) (f : H →* G) (n : N) :
    pullbackSnd S f (pullbackInl S f n) = 1 := rfl

/-- The group extension of `H` by `N` obtained by pulling `S` back along `f`. -/
def pullbackExtension (S : GroupExtension N E G) (f : H →* G) :
    GroupExtension N (PullbackTotal S f) H where
  inl := pullbackInl S f
  rightHom := pullbackSnd S f
  inl_injective := by
    intro a b h
    have h1 : S.inl a = S.inl b := by
      have hprod : (pullbackInl S f a : E × H) = (pullbackInl S f b : E × H) :=
        congrArg Subtype.val h
      have hf : (pullbackInl S f a : E × H).1 = (pullbackInl S f b : E × H).1 :=
        congrArg Prod.fst hprod
      simpa using hf
    exact S.inl_injective h1
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [MonoidHom.mem_ker]
      rfl
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hsnd : (x : E × H).2 = 1 := hx
      have hcond : S.rightHom (x : E × H).1 = f (x : E × H).2 := x.2
      rw [hsnd, map_one] at hcond
      have hker : (x : E × H).1 ∈ S.rightHom.ker := by
        rw [MonoidHom.mem_ker, hcond]
      rw [← S.range_inl_eq_ker_rightHom] at hker
      obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hker
      rw [MonoidHom.mem_range]
      use n
      apply Subtype.ext
      exact Prod.ext hn hsnd.symm
  rightHom_surjective := by
    intro h
    obtain ⟨e, he⟩ := S.rightHom_surjective (f h)
    exact ⟨⟨(e, h), he⟩, rfl⟩

end Extension

section ExtensionMap

variable {N' E' G' H' : Type*}
variable [Group N'] [Group E'] [Group G'] [Group H']
variable {S : GroupExtension N E G} {T : GroupExtension N' E' G'}

/-- The functorial pullback map, bundled as a morphism of the pullback
extensions. -/
def pullbackExtensionHom (m : S.Hom T)
    {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackExtension S f).Hom (pullbackExtension T g) where
  kernelHom := m.kernelHom
  totalHom := pullbackMap m h h_comm
  quotientHom := h
  inl_comm := by
    apply MonoidHom.ext
    intro n
    apply Subtype.ext
    apply Prod.ext
    · exact Hom.inl_comm_apply m n
    · exact map_one h
  rightHom_comm := pullbackSnd_comp_pullbackMap m h h_comm

@[simp]
theorem pullbackExtensionHom_kernelHom (m : S.Hom T)
    {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackExtensionHom m h h_comm).kernelHom = m.kernelHom := rfl

@[simp]
theorem pullbackExtensionHom_totalHom (m : S.Hom T)
    {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackExtensionHom m h h_comm).totalHom = pullbackMap m h h_comm := rfl

@[simp]
theorem pullbackExtensionHom_quotientHom (m : S.Hom T)
    {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackExtensionHom m h h_comm).quotientHom = h := rfl

@[simp]
theorem pullbackMap_comp_pullbackInl (m : S.Hom T)
    {f : H →* G} {g : H' →* G'}
    (h : H →* H') (h_comm : m.quotientHom.comp f = g.comp h) :
    (pullbackMap m h h_comm).comp (pullbackInl S f) =
      (pullbackInl T g).comp m.kernelHom :=
  (pullbackExtensionHom m h h_comm).inl_comm

end ExtensionMap

section Centrality

variable (S : GroupExtension N E G) (f : H →* G)

theorem pullback_isCentral_ker (hS : S.rightHom.ker ≤ Subgroup.center E) :
    (pullbackExtension S f).rightHom.ker ≤
      Subgroup.center (PullbackTotal S f) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  rw [MonoidHom.mem_ker] at hx
  have hsnd : (x : E × H).2 = 1 := hx
  have hcond : S.rightHom (x : E × H).1 = f (x : E × H).2 := x.2
  rw [hsnd, map_one] at hcond
  have hker : (x : E × H).1 ∈ S.rightHom.ker := by
    rw [MonoidHom.mem_ker, hcond]
  have hcenter : (x : E × H).1 ∈ Subgroup.center E := hS hker
  have h_fst : (y : E × H).1 * (x : E × H).1 = (x : E × H).1 * (y : E × H).1 :=
    Subgroup.mem_center_iff.mp hcenter (y : E × H).1
  have h_snd : (y : E × H).2 * (x : E × H).2 = (x : E × H).2 * (y : E × H).2 := by
    rw [hsnd, mul_one, one_mul]
  have hyx : y * x = x * y := by
    apply Subtype.ext
    exact Prod.ext h_fst h_snd
  exact hyx

theorem pullback_isCentral (hS : S.IsCentral) :
    (pullbackExtension S f).IsCentral :=
  pullback_isCentral_ker S f hS

end Centrality

section Identity

variable (S : GroupExtension N E G)

/-- The canonical multiplicative equivalence from the pullback along `id G` to
`E`, given by the first projection. -/
def pullbackIdEquiv : PullbackTotal S (MonoidHom.id G) ≃* E where
  toFun := pullbackFst S (MonoidHom.id G)
  invFun e := ⟨(e, S.rightHom e), by simp⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact Prod.ext rfl x.2
  right_inv := by
    intro e
    rfl
  map_mul' _ _ := rfl

/-- The extension equivalence identifying the pullback of `S` along `id G`
with `S`. -/
def pullbackIdExtensionEquiv :
    (pullbackExtension S (MonoidHom.id G)).Equiv S where
  toMulEquiv := pullbackIdEquiv S
  inl_comm := by
    funext n
    rfl
  rightHom_comm := by
    funext p
    exact p.2

end Identity

end GroupExtension
