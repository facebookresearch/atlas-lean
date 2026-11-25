/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Order

/-!
# Scottish Book Problem 142

`everyGroupIsAutomorphismGroupOfBinaryRelation` proves that every group is the full
automorphism group of a binary relation on a type in the same universe.

We encode the edges of the labeled Cayley digraph using a vertex for each edge and a
well-ordered copy of the group for the labels. An automorphism fixes the labels and
therefore preserves right multiplication by each group element.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook142Wanted

universe u

/-- **Full automorphism group of a binary relation.** Let $G$ be a group, $Z$ a set and
$X \subseteq Z \times Z$ a binary relation on $Z$. Then $G$ is the full automorphism group of
$X$ when there is an injective group homomorphism $\varphi$ from $G$ to the group of
permutations of $Z$ whose image is exactly the set of permutations $f$ of $Z$ with
$(x, y) \in X \iff (f(x), f(y)) \in X$ for all $x, y \in Z$. -/
def IsAutomorphismGroupOf (G : Type u) [Group G] (Z : Type u) (X : Set (Z × Z)) :
    Prop :=
  ∃ φ : G → Equiv.Perm Z, Function.Injective φ ∧
    (∀ g h : G, φ (g * h) = φ g * φ h) ∧
    (∀ g : G, ∀ x y : Z, (x, y) ∈ X ↔ (φ g x, φ g y) ∈ X) ∧
    ∀ f : Equiv.Perm Z, (∀ x y : Z, (x, y) ∈ X ↔ (f x, f y) ∈ X) → ∃ g : G, φ g = f

/-- The points, labels, and labeled edges of the Cayley digraph. -/
private inductive Vertex (G : Type u)
  | point : G → Vertex G
  | label : G → Vertex G
  | edge : G → G → Vertex G

/-- Loops mark the group points. An edge vertex records its source, target, and label
via the arrows `point x → edge x c → point (x * c)` and `edge x c → label c`. The labels
are also related by a strict well-order. -/
private def arc {G : Type u} [Group G] : Vertex G → Vertex G → Prop
  | .point x, .point y => x = y
  | .point x, .edge y _ => x = y
  | .edge x c, .point y => x * c = y
  | .edge _ c, .label d => c = d
  | .label c, .label d => WellOrderingRel c d
  | _, _ => False

private theorem arc_self_iff {G : Type u} [Group G] (v : Vertex G) :
    arc v v ↔ ∃ x, v = .point x := by
  cases v <;> simp [arc, irrefl]

private theorem label_iff {G : Type u} [Group G] (v : Vertex G) :
    (¬ ∃ w, arc w w ∧ arc w v) ↔ ∃ c, v = .label c := by
  cases v with
  | point x =>
    exact iff_of_false (fun h ↦ h ⟨.point x, rfl, rfl⟩) (by simp)
  | edge x c =>
    exact iff_of_false (fun h ↦ h ⟨.point x, rfl, rfl⟩) (by simp)
  | label c =>
    refine iff_of_true ?_ ⟨c, rfl⟩
    rintro ⟨w, hw, hc⟩
    obtain ⟨x, rfl⟩ := (arc_self_iff w).mp hw
    exact hc

private def translateVertex {G : Type u} [Group G] (a : G) : Vertex G → Vertex G
  | .point x => .point (a * x)
  | .label c => .label c
  | .edge x c => .edge (a * x) c

private def translate {G : Type u} [Group G] (a : G) : Equiv.Perm (Vertex G) where
  toFun := translateVertex a
  invFun := translateVertex a⁻¹
  left_inv v := by cases v <;> simp [translateVertex, ← mul_assoc]
  right_inv v := by cases v <;> simp [translateVertex, ← mul_assoc]

section

variable {G : Type u} [Group G]

private abbrev PreservesArc (f : Equiv.Perm (Vertex G)) : Prop :=
  ∀ x y, arc x y ↔ arc (f x) (f y)

private theorem exists_image_point {f : Equiv.Perm (Vertex G)} (hf : PreservesArc f)
    (x : G) : ∃ y, f (.point x) = .point y :=
  (arc_self_iff _).mp ((hf _ _).mp rfl)

private theorem exists_image_label {f : Equiv.Perm (Vertex G)} (hf : PreservesArc f)
    (c : G) : ∃ d, f (.label c) = .label d := by
  apply (label_iff _).mp
  rintro ⟨w, hw, hc⟩
  have hloop := (hf (f.symm w) (f.symm w)).mpr (by simpa using hw)
  have harc := (hf (f.symm w) (.label c)).mpr (by simpa using hc)
  exact (label_iff (.label c)).mpr ⟨c, rfl⟩ ⟨f.symm w, hloop, harc⟩

private theorem image_label {f : Equiv.Perm (Vertex G)} (hf : PreservesArc f)
    (c : G) : f (.label c) = .label c := by
  classical
  choose labelImage hlabelImage using exists_image_label hf
  have hinj : Function.Injective labelImage := by
    intro c d h
    apply Vertex.label.inj
    apply f.injective
    rw [hlabelImage c, hlabelImage d, h]
  have hsurj : Function.Surjective labelImage := by
    intro d
    have hsymm (x y) : arc x y ↔ arc (f.symm x) (f.symm y) := by
      simpa using (hf (f.symm x) (f.symm y)).symm
    obtain ⟨c, hc⟩ := exists_image_label hsymm d
    refine ⟨c, Vertex.label.inj ?_⟩
    rw [← hlabelImage c, ← hc, Equiv.apply_symm_apply]
  let e : WellOrderingRel (α := G) ≃r WellOrderingRel (α := G) :=
    RelIso.ofBijective labelImage ⟨hinj, hsurj⟩ (fun x y ↦ by
      change arc (.label (labelImage x)) (.label (labelImage y)) ↔ arc (.label x) (.label y)
      rw [← hlabelImage x, ← hlabelImage y]
      exact (hf _ _).symm)
  -- The identity and the induced label map are initial embeddings of the same well-order.
  have hc : labelImage c = c := (InitialSeg.refl _).eq_relIso e c
  simpa [hc] using hlabelImage c

private theorem image_edge {f : Equiv.Perm (Vertex G)} (hf : PreservesArc f)
    {x y : G} (c : G) (hxy : f (.point x) = .point y) :
    f (.edge x c) = .edge y c := by
  have hsource := (hf (.point x) (.edge x c)).mp rfl
  have hlabel := (hf (.edge x c) (.label c)).mp rfl
  rw [hxy] at hsource
  rw [image_label hf c] at hlabel
  generalize f (.edge x c) = v at hsource hlabel ⊢
  cases v with
  | point z => exact False.elim hlabel
  | label d => exact False.elim hsource
  | edge z d =>
    have hz : y = z := hsource
    have hd : d = c := hlabel
    rw [hz, hd]

private theorem exists_translate {f : Equiv.Perm (Vertex G)} (hf : PreservesArc f) :
    ∃ a, translate a = f := by
  obtain ⟨a, ha⟩ := exists_image_point hf 1
  -- The edge from 1 to x has label x, so its image goes from a to a * x.
  have hpoint (x : G) : f (.point x) = .point (a * x) := by
    obtain ⟨y, hy⟩ := exists_image_point hf x
    have htarget := (hf (.edge 1 x) (.point x)).mp (one_mul x)
    rw [image_edge hf x ha, hy] at htarget
    exact hy.trans (congrArg Vertex.point (show a * x = y from htarget).symm)
  refine ⟨a, Equiv.ext fun v ↦ ?_⟩
  cases v with
  | point x => exact (hpoint x).symm
  | label c => exact (image_label hf c).symm
  | edge x c => exact (image_edge hf c (hpoint x)).symm

end

/--
**Birkhoff's theorem: every group is the automorphism group of a binary relation.** For every
group $G$ there are a set $Z$ and a binary relation $X \subseteq Z \times Z$ such that $G$ is
the full automorphism group of $X$: there is an injective group homomorphism $\varphi$ from $G$
to the group of permutations of $Z$ whose image is exactly the set of permutations $f$ of $Z$
with $(x, y) \in X \iff (f(x), f(y)) \in X$ for all $x, y \in Z$.

The set $Z$ lies in the same universe as $G$.

Source: S. Ulam, Problem 142 of the Scottish Book, headed "Problem (Ulam) -
Theorem (Garrett Birkhoff)"; the representation is Birkhoff's theorem.
-/
theorem everyGroupIsAutomorphismGroupOfBinaryRelation :
    ∀ (G : Type u) [Group G], ∃ (Z : Type u) (X : Set (Z × Z)),
      IsAutomorphismGroupOf G Z X := by
  intro G _
  refine ⟨Vertex G, {p | arc p.1 p.2}, translate, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have hab := congrArg (fun e : Equiv.Perm (Vertex G) ↦ e (.point 1)) h
    exact Vertex.point.inj (by simpa [translate, translateVertex] using hab)
  · intro a b
    apply Equiv.ext
    intro v
    cases v <;> simp [Equiv.Perm.mul_apply, translate, translateVertex, mul_assoc]
  · intro a x y
    change arc x y ↔ arc (translate a x) (translate a y)
    cases x <;> cases y <;> simp [arc, translate, translateVertex, mul_assoc]
  · exact fun f hf ↦ exists_translate (f := f) hf

end MathlibExt.GroupTheory.ScottishBook142Wanted
