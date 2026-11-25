/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.FreeAlgebra
public import MathlibExt.NumberTheory.MultipleZeta.Index

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

/-- **The letter $x$ as a word.** In the free monoid on the two letters $x$ and $y$, with $x$
represented by the Boolean value false and $y$ by true, this is the word of length one
consisting of the letter $x$. -/
def xWord : FreeMonoid Bool := FreeMonoid.ofList [false]

/-- **The letter $y$ as a word.** In the free monoid on the two letters $x$ and $y$, this is the
word of length one consisting of the single letter $y$.

The letters are encoded as booleans, with $x$ as false and $y$ as true. -/
def yWord : FreeMonoid Bool := FreeMonoid.ofList [true]

/-- **Entries of an index as positive integers.** For an index $(k_1, \dots, k_r)$, this is the
list $(k_1, \dots, k_r)$ of its entries in order, each regarded as a positive integer. -/
def Index.pnatEntries : Index → List PNat
  | ⟨_, c⟩ => c.blocks.attach.map fun ⟨n, hm⟩ => ⟨n, c.blocks_pos hm⟩

/-- **Hoffman word of a list of positive integers.** For a finite list $(k_1, \dots, k_r)$ of
positive integers, this is the word $z_{k_1} z_{k_2} \cdots z_{k_r}$ in the free monoid on the two
letters $x$ and $y$, where $z_k = x^{k-1} y$ is the Hoffman block of $k$. The empty list gives the
empty word. -/
def zWordPNat (l : List PNat) : FreeMonoid Bool :=
  (l.map hoffmanBlock).prod

/-- **Hoffman word of an index.** For an index $\mathbf{k} = (k_1, \dots, k_r)$ of positive
integers, the Hoffman word of $\mathbf{k}$ is $z_{k_1} z_{k_2} \cdots z_{k_r}$ in the free monoid on
the two letters $x$ and $y$, where $z_k = x^{k-1} y$. The empty index gives the empty word. -/
def zWord (idx : Index) : FreeMonoid Bool :=
  zWordPNat idx.pnatEntries

/-- **Hoffman monomial of an index.** For an index $\mathbf{k} = (k_1, \dots, k_r)$ of positive
integers, this is the monomial $z_{k_1} z_{k_2} \cdots z_{k_r}$ with coefficient $1$ in the free
associative algebra $\mathbb{Q}\langle x, y \rangle$ over $\mathbb{Q}$ on two noncommuting letters
$x$ and $y$, where $z_k = x^{k-1} y$. In other words, it is the Hoffman word of $\mathbf{k}$ viewed
as an element of $\mathbb{Q}\langle x, y \rangle$. The empty index gives $1$. -/
noncomputable def zMonomial (idx : Index) : FreeAlgebra ℚ Bool :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).symm
    (MonoidAlgebra.single (zWord idx) 1)

/-- **Words of $\mathfrak{H}^1$.** A word $w$ in the two letters $x$ and $y$ is an
$\mathfrak{H}^1$-word when $w$ is empty or $w = uy$ for some word $u$, that is, when $w$ is
empty or ends in $y$. -/
def IsHOneWord (w : FreeMonoid Bool) : Prop :=
  w = 1 ∨ ∃ u : FreeMonoid Bool, w = u * yWord

/-- **Words of $\mathfrak{H}^0$.** A word $w$ in the two letters $x$ and $y$ is an
$\mathfrak{H}^0$-word when $w$ is empty or $w = xuy$ for some word $u$, that is, when $w$ is
empty or begins with $x$ and ends in $y$. -/
def IsHZeroWord (w : FreeMonoid Bool) : Prop :=
  w = 1 ∨ ∃ u : FreeMonoid Bool, w = xWord * u * yWord

/-- **The monoid of $\mathfrak{H}^1$-words.** This is the submonoid of the free monoid on the two
letters $x$ and $y$ consisting of the words that are empty or end in $y$. -/
def wordSubmonoidHOne : Submonoid (FreeMonoid Bool) where
  carrier := { w | IsHOneWord w }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsHOneWord] at ha hb ⊢
    rcases ha with rfl | ⟨ua, rfl⟩
    · simp only [one_mul]
      exact hb
    · rcases hb with rfl | ⟨ub, rfl⟩
      · simp
      · exact Or.inr ⟨ua * yWord * ub, by simp [mul_assoc]⟩
  one_mem' := Or.inl rfl

/-- **The monoid of $\mathfrak{H}^0$-words.** This is the submonoid of the free monoid on the two
letters $x$ and $y$ consisting of the words that are empty or begin with $x$ and end in $y$. -/
def wordSubmonoidHZero : Submonoid (FreeMonoid Bool) where
  carrier := { w | IsHZeroWord w }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsHZeroWord] at ha hb ⊢
    rcases ha with rfl | ⟨ua, rfl⟩
    · simp only [one_mul]
      exact hb
    · rcases hb with rfl | ⟨ub, rfl⟩
      · simp
      · exact Or.inr ⟨ua * yWord * xWord * ub, by simp [mul_assoc]⟩
  one_mem' := Or.inl rfl

@[simp]
theorem mem_wordSubmonoidHOne_iff (w : FreeMonoid Bool) :
    w ∈ wordSubmonoidHOne ↔ IsHOneWord w := by
  rfl

@[simp]
theorem mem_wordSubmonoidHZero_iff (w : FreeMonoid Bool) :
    w ∈ wordSubmonoidHZero ↔ IsHZeroWord w := by
  rfl

theorem wordSubmonoidHZero_le_wordSubmonoidHOne :
    wordSubmonoidHZero ≤ wordSubmonoidHOne := by
  intro w hw
  change IsHZeroWord w at hw
  change IsHOneWord w
  rcases hw with rfl | ⟨u, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨xWord * u, by simp [mul_assoc]⟩

/-- **The subalgebra $\mathfrak{H}^1$.** Let $\mathbb{Q}\langle x, y\rangle$ be the free
associative $\mathbb{Q}$-algebra on two letters $x$ and $y$, whose monomials are the words in
$x$ and $y$. The subalgebra $\mathfrak{H}^1$ of $\mathbb{Q}\langle x, y\rangle$ is the
$\mathbb{Q}$-linear span of the words that are empty or end in $y$; equivalently, it consists
of the polynomials in which every word with nonzero coefficient is empty or ends in $y$. -/
noncomputable def hOne : Subalgebra ℚ (FreeAlgebra ℚ Bool) :=
  ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).range).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toAlgHom

/-- **The subalgebra $\mathfrak{H}^0$.** Let $\mathbb{Q}\langle x, y\rangle$ be the free
associative $\mathbb{Q}$-algebra on two letters $x$ and $y$, whose monomials are the words in
$x$ and $y$. The subalgebra $\mathfrak{H}^0$ of $\mathbb{Q}\langle x, y\rangle$ is the
$\mathbb{Q}$-linear span of the words that are empty or begin with $x$ and end in $y$;
equivalently, it consists of the polynomials in which every word with nonzero coefficient is
empty or begins with $x$ and ends in $y$. -/
noncomputable def hZero : Subalgebra ℚ (FreeAlgebra ℚ Bool) :=
  ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype).range).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
      FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toAlgHom

theorem hZero_le_hOne : hZero ≤ hOne := by
  intro x hx
  simp only [hZero, hOne, Subalgebra.mem_comap, AlgHom.mem_range] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  have hle : wordSubmonoidHZero ≤ wordSubmonoidHOne :=
    wordSubmonoidHZero_le_wordSubmonoidHOne
  refine ⟨MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle) y, ?_⟩
  have hsubtype : wordSubmonoidHOne.subtype.comp (Submonoid.inclusion hle) =
      wordSubmonoidHZero.subtype :=
    Submonoid.subtype_comp_inclusion hle
  have hcomp : MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype =
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).comp
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle)) := by
    rw [← hsubtype, MonoidAlgebra.mapDomainAlgHom_comp]
  rw [hcomp] at hy
  change ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).comp
    (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle))) y =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
        FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)) x
  exact hy

theorem pnatEntries_val (idx : Index) :
    idx.pnatEntries.map PNat.val = idx.entries := by
  rcases idx with ⟨_, c⟩
  unfold Index.pnatEntries Index.entries
  rw [List.map_map]
  change c.blocks.attach.map (fun x => x.1) = c.blocks
  exact List.attach_map_subtype_val c.blocks

/-- **Empty or admissible indices.** An index is empty-or-admissible when it is admissible, that
is, nonempty with first entry at least $2$, or when it has no entries. -/
def IsHZeroIndex (idx : Index) : Prop :=
  idx.IsAdmissible ∨ idx.entries = []

/-- **The type of empty or admissible indices.** The type whose elements are the indices that
are admissible, that is, nonempty with first entry at least $2$, or that have no entries. -/
def HZeroIndex : Type := { idx : Index // IsHZeroIndex idx }

theorem zWord_eq_one_of_entries_eq_nil (idx : Index) (h : idx.entries = []) :
    zWord idx = 1 := by
  have hp : idx.pnatEntries = [] := by
    have hval := pnatEntries_val idx
    rw [h] at hval
    simpa using hval
  simp [zWord, zWordPNat, hp]

theorem zWordPNat_mem_hOne (l : List PNat) :
    zWordPNat l ∈ wordSubmonoidHOne := by
  induction l with
  | nil =>
    simp [zWordPNat, IsHOneWord, wordSubmonoidHOne]
  | cons k ks ih =>
    simp only [zWordPNat, List.map_cons, List.prod_cons]
    have hk : hoffmanBlock k ∈ wordSubmonoidHOne := by
      change IsHOneWord (hoffmanBlock k)
      refine Or.inr ⟨FreeMonoid.ofList (List.replicate (k.val - 1) false), ?_⟩
      simp only [hoffmanBlock, yWord]
      rw [FreeMonoid.ofList_append]
    exact wordSubmonoidHOne.mul_mem hk ih

theorem zWord_mem_hOne (idx : Index) :
    zWord idx ∈ wordSubmonoidHOne :=
  zWordPNat_mem_hOne idx.pnatEntries

theorem exists_hoffmanBlock_eq_xWord_mul_yWord (k : PNat) (hk : 2 ≤ k.val) :
    ∃ u, hoffmanBlock k = xWord * u * yWord := by
  refine ⟨FreeMonoid.ofList (List.replicate (k.val - 2) false), ?_⟩
  simp only [hoffmanBlock, xWord, yWord]
  have h1 : k.val - 1 = (k.val - 2) + 1 := by omega
  have h2 : List.replicate (k.val - 1) false =
      false :: List.replicate (k.val - 2) false := by
    rw [h1, List.replicate_succ]
  rw [h2, FreeMonoid.ofList_cons, FreeMonoid.ofList_append]
  simp [mul_assoc]

theorem hoffmanBlock_mem_hZero_of_two_le (k : PNat) (hk : 2 ≤ k.val) :
    hoffmanBlock k ∈ wordSubmonoidHZero := by
  obtain ⟨u, hu⟩ := exists_hoffmanBlock_eq_xWord_mul_yWord k hk
  change IsHZeroWord (hoffmanBlock k)
  exact Or.inr ⟨u, hu⟩

private theorem hZero_word_mul_hOne_mem (ua : FreeMonoid Bool) (v : FreeMonoid Bool)
    (hv : v ∈ wordSubmonoidHOne) :
    xWord * ua * yWord * v ∈ wordSubmonoidHZero := by
  change IsHOneWord v at hv
  change IsHZeroWord (xWord * ua * yWord * v)
  rcases hv with rfl | ⟨ub, rfl⟩
  · exact Or.inr ⟨ua, by simp [mul_assoc]⟩
  · exact Or.inr ⟨ua * yWord * ub, by simp [mul_assoc]⟩

theorem zWord_mem_hZero (idx : Index) (h : IsHZeroIndex idx) :
    zWord idx ∈ wordSubmonoidHZero := by
  simp only [IsHZeroIndex] at h
  rcases h with hadm | hempty
  · cases hp : idx.pnatEntries with
    | nil =>
      have hval := pnatEntries_val idx
      rw [hp] at hval
      have hempty' : idx.entries = [] := by
        simpa using hval.symm
      rw [Index.isAdmissible_iff, hempty'] at hadm
      simp at hadm
    | cons k ks =>
      have hk2 : 2 ≤ k.val := by
        have hadmList : IsAdmissible idx.entries :=
          (Index.isAdmissible_iff idx).mp hadm
        have hentries : idx.entries = k.val :: ks.map PNat.val := by
          have hval := pnatEntries_val idx
          rw [hp] at hval
          simp at hval
          exact hval.symm
        rw [hentries] at hadmList
        simpa [IsAdmissible] using hadmList
      simp only [zWord, zWordPNat, hp, List.map_cons, List.prod_cons]
      obtain ⟨u, hu⟩ := exists_hoffmanBlock_eq_xWord_mul_yWord k hk2
      rw [hu]
      exact hZero_word_mul_hOne_mem u _ (zWordPNat_mem_hOne ks)
  · have hp : idx.pnatEntries = [] := by
      have hval := pnatEntries_val idx
      rw [hempty] at hval
      simpa using hval
    simp [zWord, zWordPNat, hp, wordSubmonoidHZero, IsHZeroWord]

private theorem mem_range_mapDomainAlgHom_iff_support_subset
    (s : Submonoid (FreeMonoid Bool)) (a : MonoidAlgebra ℚ (FreeMonoid Bool)) :
    a ∈ (MonoidAlgebra.mapDomainAlgHom ℚ ℚ s.subtype).range ↔
      ∀ w ∈ a.coeff.support, w ∈ s := by
  classical
  simp only [AlgHom.mem_range, MonoidAlgebra.mapDomainAlgHom_apply]
  constructor
  · rintro ⟨b, rfl⟩ w hw
    change w ∈ (MonoidAlgebra.mapDomain s.subtype b).coeff.support at hw
    rw [MonoidAlgebra.coeff_mapDomain] at hw
    change w ∈
      (Finsupp.mapDomain (fun u : s => (u : FreeMonoid Bool)) b.coeff).support at hw
    rw [Finsupp.mapDomain_support_of_injective Subtype.coe_injective b.coeff] at hw
    simp only [Finset.mem_image] at hw
    obtain ⟨u, _, rfl⟩ := hw
    exact u.property
  · intro h
    refine ⟨MonoidAlgebra.comapDomain (fun u : s => (u : FreeMonoid Bool))
      Subtype.coe_injective a, ?_⟩
    apply MonoidAlgebra.mapDomain_comapDomain
    intro w hw
    exact ⟨⟨w, h w hw⟩, rfl⟩

theorem mem_hOne_iff_support_subset (a : FreeAlgebra ℚ Bool) :
    a ∈ hOne ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a).coeff.support,
        w ∈ wordSubmonoidHOne := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a ∈
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).range ↔ _
  exact mem_range_mapDomainAlgHom_iff_support_subset _ _

theorem mem_hZero_iff_support_subset (a : FreeAlgebra ℚ Bool) :
    a ∈ hZero ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a).coeff.support,
        w ∈ wordSubmonoidHZero := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a ∈
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype).range ↔ _
  exact mem_range_mapDomainAlgHom_iff_support_subset _ _

theorem zMonomial_mem_hOne (idx : Index) : zMonomial idx ∈ hOne := by
  rw [mem_hOne_iff_support_subset]
  simpa [zMonomial] using zWord_mem_hOne idx

theorem zMonomial_mem_hZero (idx : Index) (h : IsHZeroIndex idx) :
    zMonomial idx ∈ hZero := by
  rw [mem_hZero_iff_support_subset]
  simpa [zMonomial] using zWord_mem_hZero idx h

theorem xWord_not_mem_hOne : xWord ∉ wordSubmonoidHOne := by
  change ¬IsHOneWord xWord
  intro h
  rcases h with h | ⟨u, hu⟩
  · have hlist := congrArg FreeMonoid.toList h
    simp [xWord] at hlist
  · have hlist := congrArg FreeMonoid.toList hu
    have hlen := congrArg List.length hlist
    simp [xWord, yWord] at hlen
    simp [xWord, yWord, hlen] at hlist

theorem generatorX_not_mem_hOne : FreeAlgebra.ι ℚ (false : Bool) ∉ hOne := by
  rw [mem_hOne_iff_support_subset]
  intro h
  have hsupp :
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
        (FreeAlgebra.ι ℚ (false : Bool))).coeff.support = {xWord} := by
    have hx :
        FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
            (FreeAlgebra.ι ℚ (false : Bool)) = MonoidAlgebra.single xWord 1 := by
      simp [xWord, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
    rw [hx]
    simp
  have hxMem : xWord ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
        (FreeAlgebra.ι ℚ (false : Bool))).coeff.support := by
    rw [hsupp]
    simp
  exact xWord_not_mem_hOne (h xWord hxMem)

end MetaMathlibExt.MultipleZeta
