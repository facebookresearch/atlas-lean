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

public import MathlibExt.GroupTheory.PermutationSchurCocycle

/-!
# Bilinear Schur–Tits cocycles for monomial groups

For a skew bicharacter and parameters satisfying `ε² = 1` and `2z = 0`,
combines the Tits and Schur cocycles into a central extension of the monomial
group. Gives coefficient and projection formulas and naturality under
compatible homomorphisms.
-/

@[expose] public section

open PermutationBilinearCocycle
open PermutationBilinearTitsAction
open PermutationSchurCocycle

namespace PermutationBilinearSchurTitsCocycle

variable {n : Nat}
variable {A B : Type*} [CommGroup A] [AddCommGroup B]

/-- Tits monomial additive cocycle on `MonomialBase A (Fin n)`.

Defined by `titsAlphaAdd` on the tuple part twisted by the
permutation, plus `titsQAdd`. -/
def titsMonomialAddCocycle (b : SkewBicharacter A B) (eps : A)
    (x y : MonomialBase A (Fin n)) : B :=
  titsAlphaAdd b eps x.left (permute x.right y.left) +
    titsQAdd b eps x.right y.left

@[simp]
theorem titsMonomialAddCocycle_one_left (b : SkewBicharacter A B)
    (eps : A) (heps : eps * eps = 1)
    (y : MonomialBase A (Fin n)) :
    titsMonomialAddCocycle b eps 1 y = 0 := by
  simp [titsMonomialAddCocycle, titsAlphaAdd_one_left,
    titsQAdd_one_perm b heps]

@[simp]
theorem titsMonomialAddCocycle_one_right (b : SkewBicharacter A B)
    (eps : A) (x : MonomialBase A (Fin n)) :
    titsMonomialAddCocycle b eps x 1 = 0 := by
  simp [titsMonomialAddCocycle, titsAlphaAdd_one_right,
    titsQAdd_one_tuple]

theorem titsMonomialAddCocycle_cocycle (b : SkewBicharacter A B)
    (eps : A) (heps : eps * eps = 1)
    (x y z : MonomialBase A (Fin n)) :
    titsMonomialAddCocycle b eps x y +
        titsMonomialAddCocycle b eps (x * y) z =
      titsMonomialAddCocycle b eps y z +
        titsMonomialAddCocycle b eps x (y * z) := by
  simp only [titsMonomialAddCocycle, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, tupleActionHom_apply]
  rw [titsAlphaAdd_mul_left, permute_mul, titsQAdd_comp b heps,
    permute_mul_tuple, titsAlphaAdd_mul_right]
  have htransport := tits_transport b heps x.right y.left
    (permute y.right z.left)
  let extra :=
    titsAlphaAdd b eps x.left (permute x.right y.left) +
      titsAlphaAdd b eps x.left
        (permute x.right (permute y.right z.left)) +
      titsQAdd b eps y.right z.left
  have h := congrArg (fun t : B => t + extra) htransport.symm
  dsimp [extra] at h
  abel_nf at h ⊢
  exact h

/-- Schur-corrected Tits monomial additive cocycle.

Adds the permutation Schur cocycle with 2-torsion coefficient `z`. -/
noncomputable def schurTitsMonomialAddCocycle
    (b : SkewBicharacter A B) (eps : A) (z : B) (hz : 2 • z = 0)
    (x y : MonomialBase A (Fin n)) : B :=
  titsMonomialAddCocycle b eps x y +
    schurCocycleWith z hz x.right y.right

@[simp]
theorem schurTitsMonomialAddCocycle_one_left
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1)
    (z : B) (hz : 2 • z = 0) (y : MonomialBase A (Fin n)) :
    schurTitsMonomialAddCocycle b eps z hz 1 y = 0 := by
  simp [schurTitsMonomialAddCocycle,
    titsMonomialAddCocycle_one_left b eps heps]

@[simp]
theorem schurTitsMonomialAddCocycle_one_right
    (b : SkewBicharacter A B) (eps : A) (z : B) (hz : 2 • z = 0)
    (x : MonomialBase A (Fin n)) :
    schurTitsMonomialAddCocycle b eps z hz x 1 = 0 := by
  simp [schurTitsMonomialAddCocycle,
    titsMonomialAddCocycle_one_right]

theorem schurTitsMonomialAddCocycle_cocycle
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1)
    (z : B) (hz : 2 • z = 0)
    (x y z0 : MonomialBase A (Fin n)) :
    schurTitsMonomialAddCocycle b eps z hz x y +
        schurTitsMonomialAddCocycle b eps z hz (x * y) z0 =
      schurTitsMonomialAddCocycle b eps z hz y z0 +
        schurTitsMonomialAddCocycle b eps z hz x (y * z0) := by
  unfold schurTitsMonomialAddCocycle
  have hold := titsMonomialAddCocycle_cocycle b eps heps x y z0
  have hschur := schurWith_cocycle z hz x.right y.right z0.right
  simp only [SemidirectProduct.mul_right]
  calc
    titsMonomialAddCocycle b eps x y +
          schurCocycleWith z hz x.right y.right +
          (titsMonomialAddCocycle b eps (x * y) z0 +
            schurCocycleWith z hz (x.right * y.right) z0.right) =
        (titsMonomialAddCocycle b eps x y +
          titsMonomialAddCocycle b eps (x * y) z0) +
          (schurCocycleWith z hz x.right y.right +
            schurCocycleWith z hz (x.right * y.right) z0.right) := by
      abel
    _ = (titsMonomialAddCocycle b eps y z0 +
          titsMonomialAddCocycle b eps x (y * z0)) +
          (schurCocycleWith z hz y.right z0.right +
            schurCocycleWith z hz x.right (y.right * z0.right)) := by
      rw [hold, hschur]
    _ = titsMonomialAddCocycle b eps y z0 +
          schurCocycleWith z hz y.right z0.right +
          (titsMonomialAddCocycle b eps x (y * z0) +
            schurCocycleWith z hz x.right (y.right * z0.right)) := by
      abel

section Normalized

noncomputable def titsMonomialNormalizedCocycle
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1) :
    NormalizedCocycleExtension.NormalizedCocycle
      (MonomialBase A (Fin n)) (Multiplicative B) where
  cocycle x y :=
    Multiplicative.ofAdd (titsMonomialAddCocycle b eps x y)
  one_left y := by
    simp [titsMonomialAddCocycle_one_left b eps heps]
  one_right x := by
    simp [titsMonomialAddCocycle_one_right]
  cocycle_assoc x y z := by
    have h := titsMonomialAddCocycle_cocycle b eps heps x y z
    simpa only [← ofAdd_add, add_comm] using
      congrArg Multiplicative.ofAdd h

noncomputable def schurTitsMonomialNormalizedCocycle
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1)
    (z : B) (hz : 2 • z = 0) :
    NormalizedCocycleExtension.NormalizedCocycle
      (MonomialBase A (Fin n)) (Multiplicative B) where
  cocycle x y :=
    Multiplicative.ofAdd (schurTitsMonomialAddCocycle b eps z hz x y)
  one_left y := by
    simp [schurTitsMonomialAddCocycle_one_left b eps heps]
  one_right x := by
    simp [schurTitsMonomialAddCocycle_one_right]
  cocycle_assoc x y w := by
    have h := schurTitsMonomialAddCocycle_cocycle b eps heps z hz x y w
    simpa only [← ofAdd_add, add_comm] using
      congrArg Multiplicative.ofAdd h

end Normalized

section Extension

abbrev TitsMonomialExtension (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) :=
  NormalizedCocycleExtension.Extension
    (titsMonomialNormalizedCocycle (n := n) b eps heps)

abbrev SchurTitsMonomialExtension (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) (z : B) (hz : 2 • z = 0) :=
  NormalizedCocycleExtension.Extension
    (schurTitsMonomialNormalizedCocycle (n := n) b eps heps z hz)

noncomputable def titsMonomialGroupExtension
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1) :
    GroupExtension (Multiplicative B)
      (TitsMonomialExtension (n := n) b eps heps)
      (MonomialBase A (Fin n)) :=
  NormalizedCocycleExtension.extension
    (titsMonomialNormalizedCocycle (n := n) b eps heps)

noncomputable def schurTitsMonomialGroupExtension
    (b : SkewBicharacter A B)
    (eps : A) (heps : eps * eps = 1) (z : B) (hz : 2 • z = 0) :
    GroupExtension (Multiplicative B)
      (SchurTitsMonomialExtension (n := n) b eps heps z hz)
      (MonomialBase A (Fin n)) :=
  NormalizedCocycleExtension.extension
    (schurTitsMonomialNormalizedCocycle (n := n) b eps heps z hz)

theorem titsMonomialExtension_isCentral (b : SkewBicharacter A B)
    (eps : A) (heps : eps * eps = 1) :
    (titsMonomialGroupExtension (n := n) b eps heps).IsCentral :=
  NormalizedCocycleExtension.isCentral
    (titsMonomialNormalizedCocycle (n := n) b eps heps)

theorem schurTitsMonomialExtension_isCentral
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1)
    (z : B) (hz : 2 • z = 0) :
    (schurTitsMonomialGroupExtension (n := n) b eps heps z hz).IsCentral :=
  NormalizedCocycleExtension.isCentral
    (schurTitsMonomialNormalizedCocycle (n := n) b eps heps z hz)

@[ext]
theorem TitsMonomialExtension_ext
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {x y : TitsMonomialExtension (n := n) b eps heps}
    (h1 : x.base = y.base) (h2 : x.coeff = y.coeff) : x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[ext]
theorem SchurTitsMonomialExtension_ext
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {z : B} {hz : 2 • z = 0}
    {x y : SchurTitsMonomialExtension (n := n) b eps heps z hz}
    (h1 : x.base = y.base) (h2 : x.coeff = y.coeff) : x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[simp]
theorem TitsMonomialExtension_mul_base
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    (x y : TitsMonomialExtension (n := n) b eps heps) :
    (x * y).base = x.base * y.base :=
  rfl

@[simp]
theorem TitsMonomialExtension_mul_coeff
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    (x y : TitsMonomialExtension (n := n) b eps heps) :
    (x * y).coeff =
      x.coeff * y.coeff *
        Multiplicative.ofAdd
          (titsMonomialAddCocycle b eps x.base y.base) :=
  rfl

@[simp]
theorem TitsMonomialExtension_one_base
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1} :
    (1 : TitsMonomialExtension (n := n) b eps heps).base = 1 :=
  rfl

@[simp]
theorem TitsMonomialExtension_one_coeff
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1} :
    (1 : TitsMonomialExtension (n := n) b eps heps).coeff = 1 :=
  rfl

@[simp]
theorem SchurTitsMonomialExtension_mul_base
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {z : B} {hz : 2 • z = 0}
    (x y : SchurTitsMonomialExtension (n := n) b eps heps z hz) :
    (x * y).base = x.base * y.base :=
  rfl

@[simp]
theorem SchurTitsMonomialExtension_mul_coeff
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {z : B} {hz : 2 • z = 0}
    (x y : SchurTitsMonomialExtension (n := n) b eps heps z hz) :
    (x * y).coeff =
      x.coeff * y.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle b eps z hz x.base y.base) :=
  rfl

@[simp]
theorem SchurTitsMonomialExtension_one_base
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {z : B} {hz : 2 • z = 0} :
    (1 : SchurTitsMonomialExtension (n := n) b eps heps z hz).base = 1 :=
  rfl

@[simp]
theorem SchurTitsMonomialExtension_one_coeff
    {b : SkewBicharacter A B} {eps : A} {heps : eps * eps = 1}
    {z : B} {hz : 2 • z = 0} :
    (1 : SchurTitsMonomialExtension (n := n) b eps heps z hz).coeff = 1 :=
  rfl

end Extension

section Naturality

variable {A' B' : Type*} [CommGroup A'] [AddCommGroup B']
variable {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}

theorem titsMonomialAddCocycle_naturality
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (x y : MonomialBase A (Fin n)) :
    phi.target (titsMonomialAddCocycle b eps x y) =
      titsMonomialAddCocycle b' eps'
        (monomialBaseHom phi.source x)
        (monomialBaseHom phi.source y) := by
  unfold titsMonomialAddCocycle
  rw [map_add, titsAlphaAdd_naturality phi,
    titsQAdd_naturality phi heps]
  simp only [monomialBaseHom_left, monomialBaseHom_right,
    mapTupleHom_apply, permute_mapTuple_comm, heps]

theorem schurTitsMonomialAddCocycle_naturality
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    {z : B} {z' : B'} (hz : 2 • z = 0) (hz' : 2 • z' = 0)
    (hzmap : phi.target z = z')
    (x y : MonomialBase A (Fin n)) :
    phi.target (schurTitsMonomialAddCocycle b eps z hz x y) =
      schurTitsMonomialAddCocycle b' eps' z' hz'
        (monomialBaseHom phi.source x)
        (monomialBaseHom phi.source y) := by
  unfold schurTitsMonomialAddCocycle
  rw [map_add, titsMonomialAddCocycle_naturality phi heps,
    schurWith_naturality z hz z' hz' phi.target hzmap]
  rfl

noncomputable def titsMonomialCompatibleMap
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1) :
    NormalizedCocycleExtension.CompatibleMap
      (titsMonomialNormalizedCocycle (n := n) b eps hepsA)
      (titsMonomialNormalizedCocycle (n := n) b' eps' hepsB) where
  f := monomialBaseHom phi.source
  g := AddMonoidHom.toMultiplicative phi.target
  q := fun _ => 1
  q_one := rfl
  compat x y := by
    simp only [mul_one, one_mul]
    change Multiplicative.ofAdd
        (phi.target (titsMonomialAddCocycle b eps x y)) =
      Multiplicative.ofAdd
        (titsMonomialAddCocycle b' eps'
          (monomialBaseHom phi.source x)
          (monomialBaseHom phi.source y))
    rw [titsMonomialAddCocycle_naturality phi heps]

noncomputable def schurTitsMonomialCompatibleMap
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    {z : B} {z' : B'} (hz : 2 • z = 0) (hz' : 2 • z' = 0)
    (hzmap : phi.target z = z') :
    NormalizedCocycleExtension.CompatibleMap
      (schurTitsMonomialNormalizedCocycle (n := n) b eps hepsA z hz)
      (schurTitsMonomialNormalizedCocycle (n := n) b' eps' hepsB z' hz') where
  f := monomialBaseHom phi.source
  g := AddMonoidHom.toMultiplicative phi.target
  q := fun _ => 1
  q_one := rfl
  compat x y := by
    simp only [mul_one, one_mul]
    change Multiplicative.ofAdd
        (phi.target (schurTitsMonomialAddCocycle b eps z hz x y)) =
      Multiplicative.ofAdd
        (schurTitsMonomialAddCocycle b' eps' z' hz'
          (monomialBaseHom phi.source x)
          (monomialBaseHom phi.source y))
    rw [schurTitsMonomialAddCocycle_naturality phi heps hz hz' hzmap]

noncomputable def titsMonomialCompatibleHom
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1) :
    TitsMonomialExtension (n := n) b eps hepsA →*
      TitsMonomialExtension (n := n) b' eps' hepsB :=
  (titsMonomialCompatibleMap (n := n) phi heps hepsA hepsB).toHom

noncomputable def schurTitsMonomialCompatibleHom
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    {z : B} {z' : B'} (hz : 2 • z = 0) (hz' : 2 • z' = 0)
    (hzmap : phi.target z = z') :
    SchurTitsMonomialExtension (n := n) b eps hepsA z hz →*
      SchurTitsMonomialExtension (n := n) b' eps' hepsB z' hz' :=
  (schurTitsMonomialCompatibleMap (n := n) phi heps hepsA hepsB hz hz'
      hzmap).toHom

@[simp]
theorem titsMonomialCompatibleHom_base
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    (x : TitsMonomialExtension (n := n) b eps hepsA) :
    (titsMonomialCompatibleHom (n := n) phi heps hepsA hepsB x).base =
      monomialBaseHom phi.source x.base :=
  rfl

@[simp]
theorem titsMonomialCompatibleHom_coeff
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    (x : TitsMonomialExtension (n := n) b eps hepsA) :
    (titsMonomialCompatibleHom (n := n) phi heps hepsA hepsB x).coeff =
      AddMonoidHom.toMultiplicative phi.target x.coeff := by
  simp [titsMonomialCompatibleHom, titsMonomialCompatibleMap]

@[simp]
theorem schurTitsMonomialCompatibleHom_base
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    {z : B} {z' : B'} (hz : 2 • z = 0) (hz' : 2 • z' = 0)
    (hzmap : phi.target z = z')
    (x : SchurTitsMonomialExtension (n := n) b eps hepsA z hz) :
    (schurTitsMonomialCompatibleHom (n := n) phi heps hepsA hepsB
        hz hz' hzmap x).base =
      monomialBaseHom phi.source x.base :=
  rfl

@[simp]
theorem schurTitsMonomialCompatibleHom_coeff
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1)
    {z : B} {z' : B'} (hz : 2 • z = 0) (hz' : 2 • z' = 0)
    (hzmap : phi.target z = z')
    (x : SchurTitsMonomialExtension (n := n) b eps hepsA z hz) :
    (schurTitsMonomialCompatibleHom (n := n) phi heps hepsA hepsB
        hz hz' hzmap x).coeff =
      AddMonoidHom.toMultiplicative phi.target x.coeff := by
  simp [schurTitsMonomialCompatibleHom, schurTitsMonomialCompatibleMap]

end Naturality

end PermutationBilinearSchurTitsCocycle

end
