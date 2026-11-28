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
# Tits and Schur formulas on finite monomial groups

Let `A` be an abelian multiplicative group, `B` an abelian additive group,
and `b` a skew bicharacter from `A` to `B`. The raw Tits formula on
`Aⁿ ⋊ Sₙ` is defined for every `eps : A`. Its normalization and cocycle
theorems assume `eps * eps = 1`.

Adding the permutation Schur cocycle uses a coefficient `z : B` with
`2 • z = 0`. Under the same involution hypothesis on `eps`, both formulas
give normalized central cocycles with coefficient group `Multiplicative B`
and hence the central extensions constructed here.
-/
@[expose] public section

open PermutationBilinearCocycle
open PermutationBilinearTitsAction
open PermutationSchurCocycle

namespace PermutationBilinearSchurTitsCocycle

variable {n : Nat}
variable {A B : Type*} [CommGroup A] [AddCommGroup B]

/-- The raw Tits additive formula on `Aⁿ ⋊ Sₙ`, for an abelian
multiplicative group `A`, an abelian additive coefficient group `B`,
and a skew bicharacter `b`. It combines the bilinear tuple correction
with the permutation correction and is defined for any `eps : A`.
When `eps * eps = 1`, it is a normalized additive two-cocycle. -/
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

/-- For an abelian multiplicative group `A`, an abelian additive group
`B` and a skew bicharacter `b`, add the permutation Schur cocycle with
a coefficient `z : B` satisfying `2 • z = 0` to the raw Tits formula
on `Aⁿ ⋊ Sₙ`. The formula is defined for any `eps : A`; when
`eps * eps = 1`, it is a normalized additive two-cocycle. -/
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

/-- For abelian groups `A` and `B`, a skew bicharacter `b` and
`eps : A` with `eps * eps = 1`, the Tits formula on `Aⁿ ⋊ Sₙ`
gives a normalized central two-cocycle with coefficient group
`Multiplicative B` and trivial action. -/
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

/-- For abelian groups `A` and `B`, a skew bicharacter `b`, an element
`eps : A` with `eps * eps = 1` and a coefficient `z : B` with
`2 • z = 0`, the combined Schur and Tits formula on `Aⁿ ⋊ Sₙ`
gives a normalized central two-cocycle with coefficient group
`Multiplicative B` and trivial action. -/
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

/-- The monomial central extension defined by the Tits cocycle. -/
abbrev TitsMonomialExtension (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) :=
  NormalizedCocycleExtension.Extension
    (titsMonomialNormalizedCocycle (n := n) b eps heps)

/-- The monomial central extension defined by the combined Schur and Tits cocycle. -/
abbrev SchurTitsMonomialExtension (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) (z : B) (hz : 2 • z = 0) :=
  NormalizedCocycleExtension.Extension
    (schurTitsMonomialNormalizedCocycle (n := n) b eps heps z hz)

/-- The actual group extension associated with the monomial Tits cocycle. -/
noncomputable def titsMonomialGroupExtension
    (b : SkewBicharacter A B) (eps : A) (heps : eps * eps = 1) :
    GroupExtension (Multiplicative B)
      (TitsMonomialExtension (n := n) b eps heps)
      (MonomialBase A (Fin n)) :=
  NormalizedCocycleExtension.extension
    (titsMonomialNormalizedCocycle (n := n) b eps heps)

/-- The actual group extension associated with the combined monomial cocycle. -/
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

/-- The compatible coefficient map of the monomial Tits extensions. -/
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

/-- The compatible coefficient map of the combined monomial extensions. -/
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

/-- The group homomorphism induced by the compatible monomial Tits map. -/
noncomputable def titsMonomialCompatibleHom
    (phi : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (heps : phi.source eps = eps')
    (hepsA : eps * eps = 1) (hepsB : eps' * eps' = 1) :
    TitsMonomialExtension (n := n) b eps hepsA →*
      TitsMonomialExtension (n := n) b' eps' hepsB :=
  (titsMonomialCompatibleMap (n := n) phi heps hepsA hepsB).toHom

/-- The group homomorphism induced by the compatible combined monomial map. -/
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
