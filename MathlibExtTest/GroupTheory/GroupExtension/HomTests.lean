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

public import MathlibExt.GroupTheory.GroupExtension.Hom
public import Batteries.Tactic.Lint

/-!
# Tests for morphisms of group extensions
-/

@[expose] public section

set_option autoImplicit false

namespace GroupExtension

variable {N E G N' E' G' N'' E'' G'' : Type*}
variable [Group N] [Group E] [Group G]
variable [Group N'] [Group E'] [Group G']
variable [Group N''] [Group E''] [Group G'']
variable {S : GroupExtension N E G} {T : GroupExtension N' E' G'}
variable {U : GroupExtension N'' E'' G''}

example : S.Hom S := Hom.id S

example (f : S.Hom T) (g : T.Hom U) : S.Hom U := g.comp f

example (f : S.Hom T) : (Hom.id T).comp f = f := by simp

example (f : S.Hom T) : f.comp (Hom.id S) = f := by simp

example {f g : S.Hom T} (h : f.totalHom = g.totalHom) : f = g :=
  Hom.ext h

example {E₀ : Type*} [Group E₀]
    {V₀ : GroupExtension N E₀ G} (e : S.Equiv V₀) : S.Hom V₀ :=
  e.toHom

example {N''' E''' G''' : Type*}
    [Group N'''] [Group E'''] [Group G''']
    {V : GroupExtension N''' E''' G'''}
    (f : S.Hom T) (g : T.Hom U) (h : U.Hom V) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  Hom.comp_assoc h g f

end GroupExtension

noncomputable section

universe uN uE uG vN vE vG

namespace MathlibExtTest.GroupExtensionHomOfTotal

open GroupExtension

variable {N : Type uN} {E : Type uE} {G : Type uG}
variable {K : Type vN} {D : Type vE} {H : Type vG}
variable [Group N] [Group E] [Group G] [Group K] [Group D] [Group H]
variable {S : GroupExtension N E G} {T : GroupExtension K D H}

example (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) : S.Hom T :=
  Hom.ofTotal φ f hφ

example (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) :
    (Hom.ofTotal φ f hφ).totalHom = φ :=
  Hom.ofTotal_totalHom φ f hφ

example (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) :
    (Hom.ofTotal φ f hφ).quotientHom = f :=
  Hom.ofTotal_quotientHom φ f hφ

example (φ : E →* D) (f : G →* H)
    (hφ : T.rightHom.comp φ = f.comp S.rightHom) (n : N) :
    φ (S.inl n) = T.inl ((Hom.ofTotal φ f hφ).kernelHom n) :=
  Hom.inl_comm_apply (Hom.ofTotal φ f hφ) n

example (m : S.Hom T) :
    Hom.ofTotal m.totalHom m.quotientHom m.rightHom_comm = m :=
  Hom.ofTotal_eq m

#print axioms GroupExtension.Hom.ofTotal
#print axioms GroupExtension.Hom.ofTotal_eq
#lint only unusedArguments in MathlibExt.GroupTheory.GroupExtension.Hom

end MathlibExtTest.GroupExtensionHomOfTotal

end
