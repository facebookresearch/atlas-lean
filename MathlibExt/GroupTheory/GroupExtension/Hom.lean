/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Morphisms of group extensions

This file bundles a morphism between two group extensions, allowing both the
kernel and quotient groups to vary.  It supplies identity, composition,
extensionality, and conversion from the existing equivalence API.

Centrality is deliberately not part of the morphism data, and this file
introduces no global instances.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

namespace GroupExtension

variable {N : Type u₁} {E : Type u₂} {G : Type u₃}
variable {N' : Type v₁} {E' : Type v₂} {G' : Type v₃}
variable {N'' : Type w₁} {E'' : Type w₂} {G'' : Type w₃}
variable [Group N] [Group E] [Group G]
variable [Group N'] [Group E'] [Group G']
variable [Group N''] [Group E''] [Group G'']

/-- A morphism of group extensions, with maps on the kernel, total group,
and quotient group making both defining squares commute. -/
structure Hom (S : GroupExtension N E G) (T : GroupExtension N' E' G') where
  /-- The homomorphism between the original kernel groups. -/
  kernelHom : N →* N'
  /-- The homomorphism between the original total groups. -/
  totalHom : E →* E'
  /-- The homomorphism between the original quotient groups. -/
  quotientHom : G →* G'
  inl_comm : totalHom.comp S.inl = T.inl.comp kernelHom
  rightHom_comm : T.rightHom.comp totalHom = quotientHom.comp S.rightHom

namespace Hom

variable {S : GroupExtension N E G} {T : GroupExtension N' E' G'}
variable {U : GroupExtension N'' E'' G''}

@[simp]
theorem inl_comm_apply (f : S.Hom T) (n : N) :
    f.totalHom (S.inl n) = T.inl (f.kernelHom n) :=
  DFunLike.congr_fun f.inl_comm n

@[simp]
theorem rightHom_comm_apply (f : S.Hom T) (e : E) :
    T.rightHom (f.totalHom e) = f.quotientHom (S.rightHom e) :=
  DFunLike.congr_fun f.rightHom_comm e

/-- A morphism of extensions is determined by its map on total groups. -/
@[ext]
theorem ext {f g : S.Hom T} (h : f.totalHom = g.totalHom) : f = g := by
  have hkernel : f.kernelHom = g.kernelHom := by
    ext n
    apply T.inl_injective
    calc
      T.inl (f.kernelHom n) = f.totalHom (S.inl n) :=
        (inl_comm_apply f n).symm
      _ = g.totalHom (S.inl n) := by rw [h]
      _ = T.inl (g.kernelHom n) := inl_comm_apply g n
  have hquotient : f.quotientHom = g.quotientHom := by
    ext q
    obtain ⟨e, rfl⟩ := S.rightHom_surjective q
    calc
      f.quotientHom (S.rightHom e) = T.rightHom (f.totalHom e) :=
        (rightHom_comm_apply f e).symm
      _ = T.rightHom (g.totalHom e) := by rw [h]
      _ = g.quotientHom (S.rightHom e) := rightHom_comm_apply g e
  cases f
  cases g
  simp_all

/-- Identity morphism of a group extension. -/
def id (S : GroupExtension N E G) : S.Hom S where
  kernelHom := MonoidHom.id N
  totalHom := MonoidHom.id E
  quotientHom := MonoidHom.id G
  inl_comm := rfl
  rightHom_comm := rfl

/-- Composition of morphisms of group extensions. -/
def comp (g : T.Hom U) (f : S.Hom T) : S.Hom U where
  kernelHom := g.kernelHom.comp f.kernelHom
  totalHom := g.totalHom.comp f.totalHom
  quotientHom := g.quotientHom.comp f.quotientHom
  inl_comm := by
    rw [MonoidHom.comp_assoc, f.inl_comm, ← MonoidHom.comp_assoc,
      g.inl_comm, MonoidHom.comp_assoc]
  rightHom_comm := by
    rw [← MonoidHom.comp_assoc, g.rightHom_comm, MonoidHom.comp_assoc,
      f.rightHom_comm, ← MonoidHom.comp_assoc]

@[simp]
theorem id_kernelHom (S : GroupExtension N E G) :
    (id S).kernelHom = MonoidHom.id N := rfl

@[simp]
theorem id_totalHom (S : GroupExtension N E G) :
    (id S).totalHom = MonoidHom.id E := rfl

@[simp]
theorem id_quotientHom (S : GroupExtension N E G) :
    (id S).quotientHom = MonoidHom.id G := rfl

@[simp]
theorem comp_kernelHom (g : T.Hom U) (f : S.Hom T) :
    (g.comp f).kernelHom = g.kernelHom.comp f.kernelHom := rfl

@[simp]
theorem comp_totalHom (g : T.Hom U) (f : S.Hom T) :
    (g.comp f).totalHom = g.totalHom.comp f.totalHom := rfl

@[simp]
theorem comp_quotientHom (g : T.Hom U) (f : S.Hom T) :
    (g.comp f).quotientHom = g.quotientHom.comp f.quotientHom := rfl

@[simp]
theorem id_comp (f : S.Hom T) : (id T).comp f = f := by
  ext
  simp

@[simp]
theorem comp_id (f : S.Hom T) : f.comp (id S) = f := by
  ext
  simp

/-- Composition of morphisms of group extensions is associative. -/
theorem comp_assoc
    {N''' E''' G''' : Type*} [Group N'''] [Group E'''] [Group G''']
    {V : GroupExtension N''' E''' G'''}
    (h : U.Hom V) (g : T.Hom U) (f : S.Hom T) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

end Hom

namespace Equiv

variable {S : GroupExtension N E G}
variable {E' : Type v₂} [Group E'] {T : GroupExtension N E' G}

/-- An equivalence of extensions determines a morphism with identity maps on
the kernel and quotient. -/
def toHom (e : S.Equiv T) : S.Hom T where
  kernelHom := MonoidHom.id N
  totalHom := e.toMulEquiv.toMonoidHom
  quotientHom := MonoidHom.id G
  inl_comm := by
    ext n
    exact e.map_inl n
  rightHom_comm := by
    ext x
    exact e.rightHom_map x

@[simp]
theorem toHom_kernelHom (e : S.Equiv T) : e.toHom.kernelHom = MonoidHom.id N := rfl

@[simp]
theorem toHom_totalHom (e : S.Equiv T) :
    e.toHom.totalHom = e.toMulEquiv.toMonoidHom := rfl

@[simp]
theorem toHom_quotientHom (e : S.Equiv T) :
    e.toHom.quotientHom = MonoidHom.id G := rfl

end Equiv

namespace Hom

noncomputable section

variable {K : Type v₁} {D : Type v₂} {H : Type v₃}
variable [Group K] [Group D] [Group H]
variable {S : GroupExtension N E G} {T : GroupExtension K D H}

/-- The original kernel map induced by a whole total/base square of group extensions. -/
def kernelOfTotal (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) : N →* K :=
  (MonoidHom.ofInjective T.inl_injective).symm.toMonoidHom.comp
    ((φ.comp S.inl).codRestrict T.inl.range (fun n => by
      rw [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      change T.rightHom (φ (S.inl n)) = 1
      have h := DFunLike.congr_fun hφ (S.inl n)
      simpa only [MonoidHom.comp_apply, S.rightHom_inl, map_one] using h))

/-- An original total/base square determines its canonical map of original kernel groups. -/
def ofTotal (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) : S.Hom T where
  kernelHom := kernelOfTotal φ f hφ
  totalHom := φ
  quotientHom := f
  inl_comm := by
    ext n
    change φ (S.inl n) = T.inl ((MonoidHom.ofInjective T.inl_injective).symm _)
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  rightHom_comm := hφ

@[simp]
theorem ofTotal_totalHom (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) :
    (ofTotal φ f hφ).totalHom = φ := rfl

@[simp]
theorem ofTotal_quotientHom (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) :
    (ofTotal φ f hφ).quotientHom = f := rfl

/-- The canonical kernel reader reconstructs every original extension morphism. -/
theorem ofTotal_eq (m : S.Hom T) :
    ofTotal m.totalHom m.quotientHom m.rightHom_comm = m := by
  apply Hom.ext
  rfl

end

end Hom

end GroupExtension
