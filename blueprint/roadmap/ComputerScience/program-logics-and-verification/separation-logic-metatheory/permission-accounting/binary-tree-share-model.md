# Binary tree share model

Boolean-labelled binary trees, taken up to folding of uniform subtrees, form a Boolean algebra; the separation algebra in which disjoint trees join by pointwise disjunction is disjoint, has cross-splits, is infinitely splittable and embeds the finite and cofinite sets of naturals that model token counting.

1. *Lattice separation algebras.* Let $(A, \sqsubseteq, \sqcap, \sqcup, 0, 1)$ be a bounded distributive lattice and set $x \oplus y = z$ if and only if $x \sqcup y = z$ and $x \sqcap y = 0$. Then $(A, \oplus)$ is a separation algebra with unit $0$ satisfying disjointness and cross-split. If $A$ is a Boolean algebra, then $x \preceq y$ if and only if $x \sqsubseteq y$.
2. *Trees.* Trees are $\tau ::= \circ \mid \bullet \mid \langle \tau\ \tau \rangle$. Let $\sqsubseteq$ be the least relation with $\circ \sqsubseteq \circ$, $\circ \sqsubseteq \bullet$, $\bullet \sqsubseteq \bullet$, the congruences $\circ \cong \langle \circ\ \circ \rangle$ and $\bullet \cong \langle \bullet\ \bullet \rangle$ in both directions, and $\langle x_1\ y_1 \rangle \sqsubseteq \langle x_2\ y_2 \rangle$ whenever $x_1 \sqsubseteq x_2$ and $y_1 \sqsubseteq y_2$; write $x \cong y$ for $x \sqsubseteq y$ and $y \sqsubseteq x$. Each $\cong$-class contains a unique tree with fewest nodes, its canonical tree. On canonical trees $\sqsubseteq$ is a partial order with least element $\circ$ and greatest element $\bullet$, and joins, meets and complements are pointwise disjunction, conjunction and negation of leaves after unfolding both trees to a common shape. This is a Boolean algebra, so by part 1 canonical trees form a disjoint, cross-split separation algebra, and equality of canonical trees is decidable structurally.
3. *Splitting.* The relativization $x \bowtie y$ replaces every $\bullet$ leaf of $x$ by $y$. It satisfies $x \bowtie \bullet = x = \bullet \bowtie x$, $x \bowtie \circ = \circ = \circ \bowtie x$, $x \bowtie (y \bowtie z) = (x \bowtie y) \bowtie z$, $x \bowtie (y \sqcup z) = (x \bowtie y) \sqcup (x \bowtie z)$, $x \bowtie (y \sqcap z) = (x \bowtie y) \sqcap (x \bowtie z)$, and the injectivity laws $x \bowtie y_1 = x \bowtie y_2 \Rightarrow x = \circ \vee y_1 = y_2$ and $x_1 \bowtie y = x_2 \bowtie y \Rightarrow x_1 = x_2 \vee y = \circ$. The function $\mathrm{split}\,x = (x \bowtie \langle \bullet\ \circ \rangle,\ x \bowtie \langle \circ\ \bullet \rangle)$ makes the model infinitely splittable.
4. *Token counting.* The finite and cofinite subsets of $\mathbb{N}$ form a Boolean subalgebra of $\mathcal{P}(\mathbb{N})$. Encoding a set as the right-biased tree whose $i$-th left leaf records membership of $i$ and whose last right leaf records membership of all larger numbers is a Boolean-algebra homomorphism into trees. With $[\![p]\!]_{\mathbb{Z}} = -|p|$ for finite nonempty $p$ and $|\mathbb{N} \setminus p|$ for cofinite $p$, disjoint (co)finite sets join exactly as the counting shares do.

## Depends on

- [Positivity, disjointness and cross-split](positivity-disjointness-and-cross-split.md)
- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

- [Positivity, disjointness and cross-split](positivity-disjointness-and-cross-split.md)

## Expansion

Part 1: functionality and commutativity are clear; cancellativity holds because in a distributive lattice $x \sqcup y = x' \sqcup y$ and $x \sqcap y = x' \sqcap y$ imply $x = x'$; associativity uses distributivity to see that $y \sqcap z = 0$ and $x \sqcap (y \sqcup z) = 0$ whenever the left association is defined. Disjointness: $a \oplus a = b$ forces $a = a \sqcap a = 0$. Cross-split: take $ac = a \sqcap c$ and so on, since $a = a \sqcap (c \sqcup d) = (a \sqcap c) \sqcup (a \sqcap d)$ with $(a \sqcap c) \sqcap (a \sqcap d) \sqsubseteq c \sqcap d = 0$. In a Boolean algebra the witness for $x \sqsubseteq y \Rightarrow x \preceq y$ is $\neg x \sqcap y$. Parts 2–4 are inductions over trees, carried out in the source's Coq development. Token counting combines with splitting through a points-to $\ell \mapsto^{s,n} v$ that owns $s \bowtie [\![p]\!]_\tau$ for a (co)finite $p$ with $[\![p]\!]_{\mathbb{Z}} = n$. Missing prerequisites: bounded distributive lattices and Boolean algebras, standard in Mathlib's order library.

## Sources

- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 7, Definition 11 and equations (42)–(59), and the claims of Section 8 (definition and equation numbers of the author copy).
