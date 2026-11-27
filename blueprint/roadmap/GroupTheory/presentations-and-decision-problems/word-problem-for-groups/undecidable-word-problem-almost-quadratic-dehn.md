# A finitely presented group with undecidable word problem and almost quadratic Dehn function

There is a finitely presented group with undecidable word problem whose Dehn function is bounded by a quadratic function on an infinite set of lengths, although it is not bounded by any recursive function.

For a finite presentation $G = \langle A \mid R \rangle$, the Dehn function $f\colon \mathbb{N} \to \mathbb{N}$ is the least non-decreasing function such that every word $w$ of length at most $n$ that equals $1$ in $G$ is freely equal to a product of at most $f(n)$ conjugates of relators from $R$ and their inverses; equivalently $f(n)$ is the maximal area of minimal van Kampen diagrams with perimeter at most $n$. A function $f\colon \mathbb{N} \to \mathbb{N}$ is almost quadratic if there are a constant $C > 0$ and an infinite set $B \subseteq \mathbb{N}$ with $f(b) < Cb^2$ for all $b \in B$.

By Theorem 1.1 of the source, there exists a finitely presented group $G$ with undecidable word problem whose Dehn function is almost quadratic.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](novikov-unsolvable.md)

## Expansion

A finitely presented group has undecidable word problem exactly when its Dehn function is not bounded by a recursive function, so the Dehn function of $G$ exceeds every recursive function infinitely often while staying below $Cb^2$ on $B$. The set $B$ cannot be recursively enumerable, and contains no infinite recursively enumerable subset: an enumeration of an infinite part of $B$ would bound the area of diagrams and solve the word problem. Almost quadratic is the smallest possible growth here, since a Dehn function that is $o(n^2)$ on an infinite set forces the group to be hyperbolic, with linear Dehn function. The construction uses $S$-machines simulating a Turing machine that recognizes a recursively enumerable, non-recursive set whose good lengths form a very sparse immune set, the machine of Sapir's appendix (Theorem 14.1); a variant gives a finitely presented multiple HNN extension of a free group with undecidable conjugacy problem whose Dehn function is below $Cn^2$ on an infinite set and below $Cn^3$ everywhere (Theorem 1.3). As a corollary, $G$ has both simply connected and non-simply connected asymptotic cones (Corollary 1.2).

## Sources

- A. Yu. Olshanskii, with an appendix by M. V. Sapir, "Groups with undecidable word problem and almost quadratic Dehn function", Journal of Topology 5 (2012), no. 4, 785–886, https://doi.org/10.1112/jtopol/jts020; arXiv:1104.1476v1 (Theorem 1.1, Corollary 1.2, Theorem 1.3 and Theorem 14.1 of the appendix, of arXiv:1104.1476v1).
