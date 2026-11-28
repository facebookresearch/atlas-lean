# Commutative residuated lattices with spineless equations have undecidable word problem

For every finite set of spineless simple equations, every variety of residuated lattices between the commutative residuated lattices satisfying them and all residuated lattices has an undecidable word problem, so the corresponding extensions of $\mathsf{FL_e}$ have undecidable deducibility.

**Theorem (Galatos and St. John).** Let $\Gamma$ be a finite set of [spineless simple equations](simple-and-spineless-equations-over.md). Then every variety $\mathcal{V}$ with $\mathsf{CRL} + \Gamma \subseteq \mathcal{V} \subseteq \mathsf{RL}$ has an undecidable word problem (Theorem 5.5); hence its quasiequational theory is undecidable. In particular, for every one-variable basic equation $[n,P] : x^n \leq \bigvee_{p \in P} x^p$ such that $P$ contains at least two distinct positive integers, $\mathsf{CRL} + [n,P]$ has an undecidable word problem (Theorem 7.17).

The undecidability holds already for the $\{\vee, \cdot, 1\}$-reducts. The special case $\Gamma = \emptyset$, that every variety between $\mathsf{CRL}$ and $\mathsf{RL}$ has an undecidable word problem, is Corollary 4.6; before, only $\mathsf{RL}$ and $\mathsf{CRL}$ themselves were known to have undecidable quasiequational theories. By contrast, knotted inequalities $x^m \leq x^n$ with $m \neq n$ define subvarieties of $\mathsf{CRL}$ with decidable quasiequational theory, and the word problem of $\mathsf{CRL}$ with contraction $x \leq x^2$ is decidable.

## Depends on

- [Simple and spineless equations over commutative residuated lattices](simple-and-spineless-equations-over.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction encodes and-branching counter machines (Lincoln, Mitchell, Scedrov and Shankar), one of which has an undecidable acceptance problem, into the word problem: residuated frames built from a machine give an algebra $\mathbf{W}^+_{M}$ in $\mathsf{CRL}$ such that deciding the word problem of any variety containing it is at least as hard as acceptance (Theorem 4.5). An added equation may let the algebra accept configurations the machine does not, so for subvarieties the counter values are stored as powers $K^n$ of a large constant $K$ (exponential machines, Section 7): the equation then acts only linearly on exponents and adds no accepted configurations, provided a condition $(\star\star)$ holds. Section 8 shows, using positive linear algebra, that the equations satisfying $(\star\star)$ are exactly the spineless ones. A good expansion links pages for the undecidability of acceptance for and-branching counter machines (Lincoln, Mitchell, Scedrov and Shankar), for the residuated-frame construction of Theorem 4.5 and for the exponential machines of Section 7.

## Sources

- Nikolaos Galatos and Gavin St. John, "Most simple extensions of $\mathsf{FL_e}$ are undecidable", *The Journal of Symbolic Logic* 87(3):1156–1200, 2022, doi:10.1017/jsl.2021.46; read as arXiv:2005.00645v1, <https://arxiv.org/abs/2005.00645v1>: Theorem 5.5, Theorem 7.17, Corollary 4.6, Theorems 3.2 and 4.5, and Sections 7 and 8 of arXiv:2005.00645v1.
