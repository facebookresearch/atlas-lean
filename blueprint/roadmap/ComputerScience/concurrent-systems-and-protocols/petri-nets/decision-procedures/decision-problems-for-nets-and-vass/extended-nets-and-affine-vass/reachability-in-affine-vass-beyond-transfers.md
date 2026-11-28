# Reachability in affine VASS is undecidable for every class beyond transfers or copies

For affine vector addition systems whose matrices come from a fixed class closed under counter renaming, extension and products, reachability over $\mathbb{N}$ is undecidable unless every matrix is a permutation matrix, and reachability over $\mathbb{Z}$ is undecidable unless the class consists only of pseudo-transfer or only of pseudo-copy matrices.

**Setting (Blondin and Raskin).** An *affine VASS* of dimension $d$ has a finite set of control states and finitely many transitions $(p, A, \vec{b}, q)$ with $A \in \mathbb{Z}^{d \times d}$ and $\vec{b} \in \mathbb{Z}^d$, each mapping $p(\vec{x})$ to $q(A\vec{x} + \vec{b})$. Under *$\mathbb{N}$-reachability* every configuration along a run must have nonnegative counters; under *$\mathbb{Z}$-reachability* (integer reachability) counters range over $\mathbb{Z}$. A *class* is a set $\mathcal{C}$ of square integer matrices that contains every identity matrix and is closed under products of matrices of equal size, under counter renaming $A \mapsto P_\sigma A P_{\sigma^{-1}}$ for permutation matrices $P_\sigma$, and under extension $A \mapsto \begin{pmatrix} A & 0 \\ 0 & I_n \end{pmatrix}$. For a class $\mathcal{C}$, the problem $\mathrm{REACH}(\mathcal{C})$ (respectively $\mathbb{Z}\text{-}\mathrm{REACH}(\mathcal{C})$) asks, given an affine VASS all of whose matrices lie in $\mathcal{C}$ and configurations $p(\vec{u})$, $q(\vec{v})$, whether $q(\vec{v})$ is $\mathbb{N}$-reachable (respectively $\mathbb{Z}$-reachable) from $p(\vec{u})$. A matrix with entries in $\{-1, 0, 1\}$ is a *pseudo-transfer* matrix if it has at most one nonzero entry in each column, and a *pseudo-copy* matrix if it has at most one nonzero entry in each row.

**Theorem (Blondin and Raskin).** Let $\mathcal{C}$ be a class of matrices.

1. $\mathrm{REACH}(\mathcal{C})$ is undecidable if $\mathcal{C}$ contains a matrix that is not a permutation matrix; if all matrices of $\mathcal{C}$ are permutation matrices, it is equivalent to reachability in ordinary VASS.
2. $\mathbb{Z}\text{-}\mathrm{REACH}(\mathcal{C})$ is undecidable if $\mathcal{C}$ neither consists only of pseudo-transfer matrices nor consists only of pseudo-copy matrices.

For the remaining classes, the same paper proves integer reachability NP-complete when all matrices are diagonal with entries in $\{0, 1\}$ and PSPACE-complete otherwise. In particular, integer reachability is undecidable for every class with an infinite matrix monoid.

## Depends on

- [Vector addition systems](../../../vector-addition-systems.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Reachability for Petri nets with two reset, transfer or doubling arcs is undecidable](reachability-with-two-reset-or-transfer-arcs.md)
- [Halting is undecidable](../../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

A class that contains a matrix that is not pseudo-copy and a matrix that is not pseudo-transfer contains a matrix with an entry of absolute value at least $2$, and from it the source builds a matrix $C \in \mathcal{C}$ whose iterates grow at least by a factor $2$ at each step; this mimics the doubling steps of a reduction from the Post correspondence problem in which two counters hold the binary values of the two concatenations, giving clause 2. For clause 1, a matrix with a negative entry simulates zero tests of a two-counter Minsky machine, since applied to $\lambda \vec{e}_j$ it gives $\vec{0}$ when $\lambda = 0$ and a vector with a negative entry otherwise; a nonnegative class that is neither transfer nor copy reuses the doubling reduction; and a transfer or copy matrix that is not a permutation has a zero row or column, from which resets are built, so reachability in VASS with resets (Araki and Kasami) reduces to the problem. A good expansion links pages for the lemma giving an entry of absolute value at least $2$, and the construction of the fast-growing matrix.

## Sources

- Michael Blondin and Mikhail Raskin, *The Complexity of Reachability in Affine Vector Addition Systems with States*, Logical Methods in Computer Science 17(3), 2021, https://doi.org/10.46298/lmcs-17(3:3)2021; the definition of classes and of pseudo-transfer and pseudo-copy matrices, the trichotomy theorem for integer reachability and the dichotomy theorem for reachability over $\mathbb{N}$, with their undecidability propositions, read in arXiv:1909.02579v5. Locators in arXiv:1909.02579v5: Theorem 3.11, Corollary 3.12, Theorem 4.1, Propositions 4.3 and 4.4 and Theorem 4.5.
