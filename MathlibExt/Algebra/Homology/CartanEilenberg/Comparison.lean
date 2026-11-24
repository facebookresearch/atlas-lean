/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Basic
public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.Projective.ResolutionComparison

/-!
# Comparison maps between Cartan--Eilenberg resolutions

A chain map `g : L ⟶ L'` induces maps on boundaries, cycles, and homology.
Given supplied Cartan--Eilenberg resolutions `P` of `L` and `Q` of `L'`, a
comparison packages projective-resolution lifts of the boundary and homology
maps together with strict horseshoe comparisons of the cycle and term rows.
The cycle row in degree `j` uses the boundary lift in degree `j + 1`, while
the term row uses the boundary lift in degree `j` and reuses the cycle
comparison as its left endpoint.  Existence is asserted only under
`Nonempty`: the lifts are noncanonical, and no uniqueness is claimed.
A supplied comparison nevertheless induces strict maps of term complexes
and of bicomplexes, and supplied identity and composite comparisons
induce the identity and composite maps strictly.  Supplied comparisons
are determined by the underlying chain maps of their four constituent
families, transport along equalities of the underlying chain map, and
the supplied identity and composition operations satisfy the unit and
associativity laws after the corresponding transport.  Equality of two
supplied comparisons up to homotopy, and any spectral or right-edge
naturality, are not claimed here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L L' : ChainComplex C ℕ}
variable (P : CartanEilenbergResolution L) (Q : CartanEilenbergResolution L')
variable (g : L ⟶ L')

namespace CartanEilenbergResolution

/-- A supplied comparison of Cartan--Eilenberg resolutions over a chain map.

The four families are the boundary and homology endpoint lifts and the
strict horseshoe comparisons of the cycle and term rows.  In degree `j`
the cycle comparison has left endpoint `boundaryHom (j + 1)` and right
endpoint `homologyHom j`; the term comparison has left endpoint the cycle
comparison bundled as a morphism of cycle resolutions and right endpoint
`boundaryHom j`.  Lower-triangular coordinate formulas in Mathlib's
`Biprod.ofComponents` convention (vanishing left-endpoint-to-right-endpoint'
component, free right-endpoint-to-left-endpoint' cross component) are not
stored: they are derived by `Hom.cyclesHom_spec` and `Hom.termHom_spec`. -/
structure Hom where
  /-- Lifts of the maps on outgoing boundary objects. -/
  boundaryHom (j : ℕ) :
    ProjectiveResolution.Hom (P.boundaryResolution j)
      (Q.boundaryResolution j) (boundaryFromMap g j)
  /-- Lifts of the maps on homology objects. -/
  homologyHom (j : ℕ) :
    ProjectiveResolution.Hom (P.homologyResolution j)
      (Q.homologyResolution j) (homologyMap g j)
  /-- Strict comparisons of the boundary--cycle--homology horseshoe rows. -/
  cyclesHom (j : ℕ) :
    ProjectiveResolution.HorseshoeData.Hom
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := boundaryHom (j + 1)) (w := homologyHom j)
  /-- Strict comparisons of the cycle--term--boundary horseshoe rows. -/
  termHom (j : ℕ) :
    ProjectiveResolution.HorseshoeData.Hom
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (cyclesHom j).toProjectiveResolutionHom)
      (w := boundaryHom j)

namespace Hom

/-- Two supplied comparisons over the same chain map are equal once the
underlying chain maps of all four constituent families agree in every
original degree; every remaining field of the constituents is a
proof. -/
@[ext]
theorem ext {F G : Hom P Q g}
    (hb : ∀ j : ℕ, (F.boundaryHom j).hom = (G.boundaryHom j).hom)
    (hh : ∀ j : ℕ, (F.homologyHom j).hom = (G.homologyHom j).hom)
    (hc : ∀ j : ℕ, (F.cyclesHom j).hom = (G.cyclesHom j).hom)
    (ht : ∀ j : ℕ, (F.termHom j).hom = (G.termHom j).hom) : F = G := by
  obtain ⟨bF, hF, cF, tF⟩ := F
  obtain ⟨bG, hG, cG, tG⟩ := G
  have hb' : bF = bG :=
    funext fun j => ProjectiveResolution.Hom.ext (hb j)
  have hh' : hF = hG :=
    funext fun j => ProjectiveResolution.Hom.ext (hh j)
  subst hb'
  subst hh'
  have hc' : cF = cG :=
    funext fun j =>
      ProjectiveResolution.HorseshoeData.Hom.ext (h := hc j)
  subst hc'
  have ht' : tF = tG :=
    funext fun j =>
      ProjectiveResolution.HorseshoeData.Hom.ext (h := ht j)
  subst ht'
  rfl

/-- The cycle comparisons have the forced lower-triangular coordinate
formula (in Mathlib's `Biprod.ofComponents` convention: vanishing
boundary-resolution-to-homology-resolution' component, free
homology-resolution-to-boundary-resolution' cross component) in the stored
cycle horseshoe coordinates. -/
theorem cyclesHom_spec (F : Hom P Q g) (j : ℕ) :
    (F.cyclesHom j).Spec
      (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j) :=
  (F.cyclesHom j).spec
    (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j)

/-- The term comparisons have the forced lower-triangular coordinate
formula (in Mathlib's `Biprod.ofComponents` convention: vanishing
cycle-resolution-to-boundary-resolution' component, free
boundary-resolution-to-cycle-resolution' cross component) in the stored
term horseshoe coordinates. -/
theorem termHom_spec (F : Hom P Q g) (j : ℕ) :
    (F.termHom j).Spec (sH := P.termSpec j) (sH' := Q.termSpec j) :=
  (F.termHom j).spec (sH := P.termSpec j) (sH' := Q.termSpec j)

/-- The term comparisons strictly commute with the lifted original-chain
differentials.  The proof pastes the three horseshoe squares
`termHom (j+1)` projection, `cyclesHom j` inclusion, and `termHom j`
inclusion; no sign occurs. -/
@[reassoc]
theorem termDifferential_naturality (F : Hom P Q g) (j : ℕ) :
    (F.termHom (j + 1)).hom ≫ Q.termDifferential j =
      P.termDifferential j ≫ (F.termHom j).hom := by
  have hterm : (P.termHorseshoe j).i ≫ (F.termHom j).hom =
      (F.cyclesHom j).hom ≫ (Q.termHorseshoe j).i :=
    (F.termHom j).comm_i
  rw [P.termDifferential_eq j, Q.termDifferential_eq j]
  simp only [Category.assoc]
  rw [reassoc_of% (F.termHom (j + 1)).comm_p]
  rw [← reassoc_of% (F.cyclesHom j).comm_i]
  rw [← hterm]

/-- The strict map of original-degree complexes of term resolutions
induced by a supplied comparison.  Its component in degree `j` is the
term comparison `F.termHom j`. -/
noncomputable def termComplexHom (F : Hom P Q g) :
    P.termComplex ⟶ Q.termComplex :=
  ChainComplex.ofHom (fun j => (F.termHom j).hom) (fun j => by
    rw [P.termComplex_d j, Q.termComplex_d j]
    exact termDifferential_naturality P Q g F j)

@[simp]
theorem termComplexHom_f (F : Hom P Q g) (j : ℕ) :
    F.termComplexHom.f j = (F.termHom j).hom :=
  rfl

/-- The strict map of Cartan--Eilenberg bicomplexes induced by a
supplied comparison, obtained by flipping the term-complex map. -/
noncomputable def bicomplexHom (F : Hom P Q g) :
    P.bicomplex ⟶ Q.bicomplex :=
  (HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)).map F.termComplexHom

@[simp]
theorem bicomplexHom_f_f (F : Hom P Q g) (a j : ℕ) :
    (F.bicomplexHom.f a).f j = (F.termHom j).hom.f a :=
  rfl

/-- The supplied identity comparison of a Cartan--Eilenberg resolution
with itself, over the identity chain map.  Its four underlying chain
maps are identities; the endpoint lifts are transported along
`boundaryFromMap_id` and `homologyMap_id`, and the horseshoe
comparisons are the identity horseshoe comparisons transported along
`boundaryCyclesHomologyMap_id` and `cyclesTermBoundaryMap_id`.  An
arbitrary comparison over `𝟙 L` is not asserted to equal this one. -/
def id (P : CartanEilenbergResolution L) : Hom P P (𝟙 L) where
  boundaryHom j := (ProjectiveResolution.Hom.id
    (P.boundaryResolution j)).cast (boundaryFromMap_id L j).symm
  homologyHom j := (ProjectiveResolution.Hom.id
    (P.homologyResolution j)).cast (homologyMap_id L j).symm
  cyclesHom j :=
    (ProjectiveResolution.HorseshoeData.Hom.id (P.cyclesHorseshoe j)).cast
      (boundaryCyclesHomologyMap_id L j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)
  termHom j :=
    (ProjectiveResolution.HorseshoeData.Hom.id (P.termHorseshoe j)).cast
      (cyclesTermBoundaryMap_id L j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)

@[simp]
theorem id_boundaryHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).boundaryHom j).hom =
      𝟙 (P.boundaryResolution j).complex :=
  rfl

@[simp]
theorem id_homologyHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).homologyHom j).hom =
      𝟙 (P.homologyResolution j).complex :=
  rfl

@[simp]
theorem id_cyclesHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).cyclesHom j).hom =
      𝟙 (P.cyclesResolution j).complex :=
  rfl

@[simp]
theorem id_termHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).termHom j).hom = 𝟙 (P.termResolution j).complex :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two supplied comparisons of Cartan--Eilenberg
resolutions.  Its four underlying chain maps are the composites of the
constituents; the endpoint lifts are transported along
`boundaryFromMap_comp` and `homologyMap_comp`, and the horseshoe
comparisons are the composites of the constituent horseshoe comparisons
transported along `boundaryCyclesHomologyMap_comp` and
`cyclesTermBoundaryMap_comp`.  An arbitrary comparison over `g ≫ h` is
not asserted to equal this composite. -/
def comp {L'' : ChainComplex C ℕ} {R : CartanEilenbergResolution L''}
    {h : L' ⟶ L''} (F : Hom P Q g) (G : Hom Q R h) : Hom P R (g ≫ h) where
  boundaryHom j := ((F.boundaryHom j).comp (G.boundaryHom j)).cast
    (boundaryFromMap_comp g h j).symm
  homologyHom j := ((F.homologyHom j).comp (G.homologyHom j)).cast
    (homologyMap_comp g h j).symm
  cyclesHom j :=
    ((F.cyclesHom j).comp (G.cyclesHom j)).cast
      (boundaryCyclesHomologyMap_comp g h j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)
  termHom j :=
    ((F.termHom j).comp (G.termHom j)).cast
      (cyclesTermBoundaryMap_comp g h j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)

@[simp]
theorem comp_boundaryHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).boundaryHom j).hom =
      (F.boundaryHom j).hom ≫ (G.boundaryHom j).hom :=
  rfl

@[simp]
theorem comp_homologyHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).homologyHom j).hom =
      (F.homologyHom j).hom ≫ (G.homologyHom j).hom :=
  rfl

@[simp]
theorem comp_cyclesHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).cyclesHom j).hom =
      (F.cyclesHom j).hom ≫ (G.cyclesHom j).hom :=
  rfl

@[simp]
theorem comp_termHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).termHom j).hom =
      (F.termHom j).hom ≫ (G.termHom j).hom :=
  rfl

/-- Transport a supplied comparison along an equality of the underlying
chain maps.  The underlying chain maps of all four constituent families
are unchanged, as are the induced term-complex and bicomplex maps.  The
resolutions and chain maps are implicit, as for
`ProjectiveResolution.Hom.cast`, so transport is used as `F.cast h`. -/
def cast {P : CartanEilenbergResolution L}
    {Q : CartanEilenbergResolution L'} {g g' : L ⟶ L'}
    (F : Hom P Q g) (h : g = g') : Hom P Q g' :=
  h ▸ F

@[simp]
theorem cast_rfl (F : Hom P Q g) : F.cast rfl = F :=
  rfl

@[simp]
theorem cast_cast {g' g'' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (h' : g' = g'') : (F.cast h).cast h' = F.cast (h.trans h') := by
  cases h
  cases h'
  rfl

@[simp]
theorem cast_boundaryHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).boundaryHom j).hom = (F.boundaryHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_homologyHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).homologyHom j).hom = (F.homologyHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_cyclesHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).cyclesHom j).hom = (F.cyclesHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_termHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).termHom j).hom = (F.termHom j).hom := by
  cases h
  rfl

/-- Transporting a supplied comparison transports its boundary
endpoint lifts by the corresponding transport of resolution
morphisms. -/
theorem cast_boundaryHom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) : (F.cast h).boundaryHom j =
      (F.boundaryHom j).cast
        (congrArg (fun k => boundaryFromMap k j) h) := by
  ext
  simp

/-- Transporting a supplied comparison transports its homology
endpoint lifts by the corresponding transport of resolution
morphisms. -/
theorem cast_homologyHom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) : (F.cast h).homologyHom j =
      (F.homologyHom j).cast
        (congrArg (fun k => homologyMap k j) h) := by
  ext
  simp

@[simp]
theorem termComplexHom_cast {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g') :
    (F.cast h).termComplexHom = F.termComplexHom := by
  cases h
  rfl

@[simp]
theorem bicomplexHom_cast {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g') :
    (F.cast h).bicomplexHom = F.bicomplexHom := by
  cases h
  rfl

/-- The supplied identity comparison induces the identity map of term
complexes, strictly. -/
@[simp]
theorem termComplexHom_id (P : CartanEilenbergResolution L) :
    (Hom.id P).termComplexHom = 𝟙 P.termComplex := by
  ext j
  simp

/-- The composite of supplied comparisons induces the composite map of
term complexes, strictly. -/
@[simp]
theorem termComplexHom_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) :
    (Hom.comp P Q g F G).termComplexHom =
      F.termComplexHom ≫ G.termComplexHom := by
  ext j
  simp

/-- The supplied identity comparison induces the identity map of
bicomplexes, strictly. -/
@[simp]
theorem bicomplexHom_id (P : CartanEilenbergResolution L) :
    (Hom.id P).bicomplexHom = 𝟙 P.bicomplex := by
  ext a j
  simp

/-- The composite of supplied comparisons induces the composite map of
bicomplexes, strictly. -/
@[simp]
theorem bicomplexHom_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) :
    (Hom.comp P Q g F G).bicomplexHom = F.bicomplexHom ≫ G.bicomplexHom := by
  ext a j
  simp

/-- Left unit law for supplied comparisons: composing the supplied
identity comparison with a supplied comparison, transported along
`Category.id_comp` of the underlying chain maps, is the supplied
comparison itself. -/
theorem id_comp (F : Hom P Q g) :
    (Hom.comp P P (𝟙 L) (Hom.id P) F).cast (Category.id_comp g) = F := by
  ext j <;> simp

/-- Right unit law for supplied comparisons: composing a supplied
comparison with the supplied identity comparison, transported along
`Category.comp_id` of the underlying chain maps, is the supplied
comparison itself. -/
theorem comp_id (F : Hom P Q g) :
    (Hom.comp P Q g F (Hom.id Q)).cast (Category.comp_id g) = F := by
  ext j <;> simp

/-- Associativity for supplied comparisons, transported along
`Category.assoc` of the underlying chain maps. -/
theorem assoc {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    {L''' : ChainComplex C ℕ} {S : CartanEilenbergResolution L'''}
    {k : L'' ⟶ L'''} (F : Hom P Q g) (G : Hom Q R h) (H : Hom R S k) :
    (Hom.comp P R (g ≫ h) (Hom.comp P Q g F G) H).cast
        (Category.assoc g h k) =
      Hom.comp P Q g F (Hom.comp Q R h G H) := by
  ext j <;> simp

end Hom

/-- A comparison of supplied Cartan--Eilenberg resolutions exists over
every chain map.  The boundary and homology lifts and both horseshoe
middle maps are chosen noncanonically. -/
theorem nonempty_hom : Nonempty (Hom P Q g) := by
  let beta (j : ℕ) :
      ProjectiveResolution.Hom (P.boundaryResolution j)
        (Q.boundaryResolution j) (boundaryFromMap g j) :=
    ProjectiveResolution.liftHom (boundaryFromMap g j)
      (P.boundaryResolution j) (Q.boundaryResolution j)
  let eta (j : ℕ) :
      ProjectiveResolution.Hom (P.homologyResolution j)
        (Q.homologyResolution j) (homologyMap g j) :=
    ProjectiveResolution.liftHom (homologyMap g j)
      (P.homologyResolution j) (Q.homologyResolution j)
  have hZ (j : ℕ) : Nonempty (ProjectiveResolution.HorseshoeData.Hom
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := beta (j + 1)) (w := eta j)) :=
    ProjectiveResolution.HorseshoeData.nonempty_hom
      (hS := L.boundaryCyclesHomologyShortExact j)
      (hS' := L'.boundaryCyclesHomologyShortExact j)
      (P₁ := P.boundaryResolution (j + 1))
      (P₃ := P.homologyResolution j)
      (P₁' := Q.boundaryResolution (j + 1))
      (P₃' := Q.homologyResolution j)
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := beta (j + 1)) (w := eta j)
  let zeta (j : ℕ) := (hZ j).some
  have hT (j : ℕ) : Nonempty (ProjectiveResolution.HorseshoeData.Hom
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (zeta j).toProjectiveResolutionHom) (w := beta j)) :=
    ProjectiveResolution.HorseshoeData.nonempty_hom
      (hS := L.cyclesTermBoundaryShortExact j)
      (hS' := L'.cyclesTermBoundaryShortExact j)
      (P₁ := (P.cyclesHorseshoe j).middle)
      (P₃ := P.boundaryResolution j)
      (P₁' := (Q.cyclesHorseshoe j).middle)
      (P₃' := Q.boundaryResolution j)
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (sH := P.termSpec j) (sH' := Q.termSpec j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (zeta j).toProjectiveResolutionHom) (w := beta j)
  let tau (j : ℕ) := (hT j).some
  exact ⟨⟨beta, eta, zeta, tau⟩⟩

end CartanEilenbergResolution

end HomologicalComplex

end
