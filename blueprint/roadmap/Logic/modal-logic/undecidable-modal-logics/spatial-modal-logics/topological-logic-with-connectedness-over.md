# Topological logic with connectedness is undecidable over Euclidean polyhedra

Satisfiability of quantifier-free Boolean combinations of region terms with a connectedness predicate is undecidable over the regular closed polyhedra of every Euclidean space of dimension at least 2, and over the regular closed sets of the plane; so is the variant with a predicate for having a connected interior, over the plane.

**Languages.** $\mathcal{B}c$ is the quantifier-free fragment of first-order logic in the signature $(+, \cdot, -, 0, 1, c)$ with a unary predicate $c$; $\mathcal{B}c^\circ$ is the same with a unary predicate $c^\circ$ in place of $c$.

**Interpretations.** A set $X \subseteq \mathbb{R}^n$ is *regular closed* if it is the closure of an open set, and *polyhedral* if it is a finite union of finite intersections of closed half-spaces. $\mathrm{RC}(\mathbb{R}^n)$ is the Boolean algebra of regular closed subsets of $\mathbb{R}^n$ under inclusion, and $\mathrm{RCP}(\mathbb{R}^n)$ its subalgebra of regular closed polyhedra. Formulas are interpreted by taking $+, \cdot, -, 0, 1$ as the Boolean operations of these algebras, $c(r)$ as "$r$ is connected" and $c^\circ(r)$ as "the interior of $r$ is connected", where a set is connected if, with the subspace topology, it is not the union of two disjoint nonempty closed subsets; in particular the empty region $0$ satisfies both $c$ and $c^\circ$. The *satisfiability problem* asks whether some assignment of elements of the algebra to the variables of a formula makes it true.

**Theorem (Kontchakov, Nenov, Pratt-Hartmann and Zakharyaschev).**

1. For every $n \geq 2$, satisfiability of $\mathcal{B}c$ over $\mathrm{RCP}(\mathbb{R}^n)$ is r.e.-hard (Corollary 10).
2. Satisfiability of $\mathcal{B}c$ over $\mathrm{RC}(\mathbb{R}^2)$ and over $\mathrm{RCP}(\mathbb{R}^2)$ is r.e.-hard (Theorem 20).
3. Satisfiability of $\mathcal{B}c^\circ$ over $\mathrm{RC}(\mathbb{R}^2)$ and over $\mathrm{RCP}(\mathbb{R}^2)$ is r.e.-hard (Theorem 21).

All these problems are therefore undecidable. By contrast, satisfiability of $\mathcal{B}c^\circ$ is NP-complete over $\mathrm{RC}(\mathbb{R}^n)$ and EXPTIME-complete over $\mathrm{RCP}(\mathbb{R}^n)$ for $n \geq 3$, and both languages are NP-complete over $\mathbb{R}$; decidability of $\mathcal{B}c$ over $\mathrm{RC}(\mathbb{R}^n)$ for $n \geq 3$ is left open by the source.

## Depends on

- [Topological space](../../../../Topology/topological-spaces/topological-space.md)
- [Interior of a subset](../../../../Topology/topological-spaces/open-and-closed-sets/interior-of-subset.md)
- [Closure of a subset](../../../../Topology/topological-spaces/open-and-closed-sets/closure-of-subset.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

For an instance of the Post correspondence problem a conjunction of literals is built that is satisfiable over $\mathrm{RCP}(\mathbb{R}^n)$ if the instance has a solution, and that is satisfiable over a unicoherent, finitely decomposable frame only if the instance has a solution (Theorem 8, for a language with an additional contact predicate); the contact predicate is then eliminated, giving clause 1. The planar results use a separate construction with regions that have infinitely many components. Since $\mathbb{R}^n$ is unicoherent (Kuratowski, as cited in Section 2 of the source), both directions apply to the Euclidean frames. A good expansion links pages for the reduction of Theorem 8, the unicoherence of $\mathbb{R}^n$, the elimination of the contact predicate (as in the proof of Theorem 7, used for Corollary 10), and the planar constructions of Theorems 20 and 21.

## Sources

- R. Kontchakov, Y. Nenov, I. Pratt-Hartmann and M. Zakharyaschev, "Topological logics with connectedness over Euclidean spaces", *ACM Transactions on Computational Logic* 14(2):1–48, 2013, doi:10.1145/2480759.2480765; read as arXiv:1110.4034v1, <https://arxiv.org/abs/1110.4034v1>: the abstract, Section 1, Theorem 8 and Corollary 10 (Section 4), Theorems 20 and 21 (Section 5), and the results on $\mathcal{B}c^\circ$ in higher dimensions.
