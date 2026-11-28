# Atomic Kripke models

An atomic Kripke model is a Kripke model whose states, transitions and labelling are finitely supported sets with atoms, so that it may have infinitely many states while being finitely describable when it is orbit-finite.

**Sets with atoms.** Fix a countably infinite set $\mathbb A$ of *atoms*, either with equality only (*equality atoms*) or ordered as the rationals $(\mathbb Q, <)$ (*ordered atoms*, a countable dense linear order without endpoints), and let $\mathrm{Aut}(\mathbb A)$ be its automorphism group, acting on the von Neumann-like universe of sets built from atoms. A finite $S \subseteq \mathbb A$ *supports* a set $x$ if every automorphism fixing $S$ pointwise fixes $x$; $x$ is *equivariant* if $\emptyset$ supports it. A finitely supported set is *orbit-finite* if it is a finite union of orbits under the automorphisms fixing some support. A *set with atoms* is a set in this universe that is hereditarily finitely supported: it, its elements, their elements, and so on, are all finitely supported (Section 3.1 of the source); only such sets are considered. For example $\mathbb A$ and $\mathbb A^n$ are equivariant and orbit-finite, while $\mathbb A^*$ is not orbit-finite, and the powerset of $\mathbb A$ is equivariant but not a set with atoms, since some of its elements are not finitely supported (Example 3.3).

**Definition.** For an equivariant set $P$ of basic propositions, an *atomic Kripke model* $\mathcal K = \langle K, \to, \models\rangle$ consists of a set with atoms $K$, a finitely supported transition relation $\to \subseteq K \times K$ and a finitely supported relation $\models \subseteq K \times P$; it is *orbit-finite* if $K$ is, and *deterministic* if every state has exactly one successor.

## Depends on

- [Kripke model](../../modal-logic/kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Remarks

Every classical set is an equivariant set with atoms whose elements are their own orbits, so a classical Kripke model is an atomic one, and it is orbit-finite exactly when it is finite. The atomic μ-calculus, atomic CTL* and atomic LTL are interpreted over these models.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 2 (deterministic Kripke models, in the paragraph on LTL after Definition 2.5), Section 3 (sets with atoms, equality and ordered atoms, Example 3.3) and Section 4 (Definition 4.4).
