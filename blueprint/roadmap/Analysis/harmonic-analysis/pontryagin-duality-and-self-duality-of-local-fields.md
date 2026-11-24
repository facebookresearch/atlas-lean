# Pontryagin duality and the self-duality of local fields

This node is still to be broken down. It covers the duality theory of locally compact abelian groups that
the page on Heisenberg groups and the Stone–von Neumann theorem uses.

- **Pontryagin duality.** For a locally compact Hausdorff abelian group $L$, the Pontryagin dual $\hat L$ is the
  group of continuous homomorphisms $L \to \mathbb{T} = \mathbb{R}/\mathbb{Z}$ with the compact-open topology;
  it is a locally compact abelian group, and $\varphi \colon L \to \hat{\hat L}$, $\varphi(x)(\chi) = \chi(x)$, is an
  isomorphism of topological groups. The dual of a compact group is discrete and the dual of a discrete group is
  compact.
- **Self-duality of local fields.** Let $F$ be a local field (a locally compact non-discrete field) and
  $\psi \colon F \to \mathbb{S}^1 = \{z \in \mathbb{C} : \lvert z \rvert = 1\}$ a nontrivial continuous additive character,
  unitary by definition. Then $a \mapsto \psi(a \,\cdot)$ is an isomorphism of topological groups from $F$ onto its
  Pontryagin dual, the unitary characters being identified with homomorphisms to $\mathbb{T}$ through
  $t \mapsto e^{2\pi i t}$. Non-unitary continuous characters are excluded: $x \mapsto e^x$ on $\mathbb{R}$ is not of the form
  $\psi(a \, \cdot)$.

## Expansion

A good expansion has statement pages for Pontryagin duality, for the duality between compact and discrete
abelian groups, and for the self-duality of local fields, each citing the sources below with locators.
Prasad deduces Pontryagin duality for groups with a compact open subgroup from the Peter–Weyl theorem, and
in general from the structure theorem $L \cong E \times \mathbb{R}^n$ with $E$ having a compact open subgroup.

## Depends on

- [Topological group](../../Topology/topological-groups/topological-group.md), for the setting

## Proof depends on

- [Unitary representations of locally compact groups and representations of compact groups](../../RepresentationTheory/lie-and-topological-representations/unitary-representations-and-representations-of-compact-groups.md), for
  the Peter–Weyl theorem behind the duality of compact and discrete groups

## Sources

- A. Prasad, "An easy proof of the Stone–von Neumann–Mackey theorem", arXiv:0912.0574 (2009): §2 (the
  Pontryagin dual, the Pontryagin–van Kampen structure theorem and the Pontryagin duality theorem, with the
  reduction of the latter to groups with a compact open subgroup and to $\mathbb{R}^n$) and §§3.3–3.4 (compact and
  discrete groups; groups with compact open subgroups, such as $\mathbb{Q}_p$).
- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: §4.3, Theorem 4.4, p. 14 (for a local field $F$ and a nontrivial
  character $\psi$, $a \mapsto \psi(a\,\cdot)$ is an isomorphism of $F$ onto its Pontryagin dual).
