# Every recursively enumerable set over a polynomial ring over a finite field is Diophantine

For a finite field $\mathbb{F}_q$, every recursively enumerable subset of $\mathbb{F}_q[Z]^k$ is Diophantine over $\mathbb{F}_q[Z]$, the analogue for polynomial rings over finite fields of the Davis–Putnam–Robinson–Matiyasevich theorem.

Let $\mathbb{F}_q$ be a finite field of characteristic $p$ and $\alpha$ an element with $\mathbb{F}_q = \mathbb{F}_p(\alpha)$. Work in the language $\{+, \cdot, 0, 1, \alpha, Z\}$, interpreted in the polynomial ring $\mathbb{F}_q[Z]$, whose elements are encoded as finite strings in the usual way. For $k \ge 1$, a set $S \subseteq \mathbb{F}_q[Z]^k$ is *Diophantine over $\mathbb{F}_q[Z]$* if there is a polynomial $P(x_1, \dots, x_k, y_1, \dots, y_m)$ with coefficients in $\mathbb{Z}[\alpha, Z]$ such that

$$
(a_1, \dots, a_k) \in S \iff \exists\, b_1, \dots, b_m \in \mathbb{F}_q[Z] :\ P(a_1, \dots, a_k, b_1, \dots, b_m) = 0 .
$$

It is *recursively enumerable* if some algorithm lists exactly its elements.

**Theorem (Demeyer).** For every finite field $\mathbb{F}_q$ and every $k \ge 1$, every recursively enumerable subset of $\mathbb{F}_q[Z]^k$ is Diophantine over $\mathbb{F}_q[Z]$.

The converse holds trivially, so the Diophantine sets over $\mathbb{F}_q[Z]$ are exactly the recursively enumerable ones. The source also treats a recursive infinite algebraic extension $F$ of $\mathbb{F}_p$: the Diophantine subsets of $F[Z]^k$ are exactly the recursively enumerable sets that are fixed under a Frobenius automorphism (Theorem 11 of the copy read). Undecidability of the existential theory of $\mathbb{F}_q[Z]$ in the language of rings with a constant for $Z$ was known earlier, from Denef's work on [polynomial rings over integral domains](polynomial-rings-are-existentially-undecidable.md).

## Depends on

- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)

## Proof depends on

None.

## Expansion

An earlier paper of the author shows that every recursively enumerable relation over $\mathbb{F}_q[Z]$ is Diophantine over the two-variable ring $\mathbb{F}_q[W, Z]$. The new step is a Diophantine interpretation of $\mathbb{F}_q[W, Z]$ over $\mathbb{F}_q[Z]$ (Sections 2 to 4 of the copy read), in which polynomials in two variables are encoded by triples in a Diophantine set $M$ of $(w, s)$-representations. Transporting the Diophantine definition of $S(V) \subseteq \mathbb{F}_q[V, W]$ through this interpretation gives a Diophantine definition of an r.e. set $S \subseteq \mathbb{F}_q[Z]$; the case $k \ge 2$ follows with the Diophantine pairing function $(A, B) \mapsto A^p Z + B^p$, an injection of $\mathbb{F}_q[Z]^2$ into $\mathbb{F}_q[Z]$ (Section 5). A good expansion links the two-variable result of the earlier paper (Demeyer, Journal of Algebra 310 (2007), 801–828, https://doi.org/10.1016/j.jalgebra.2006.09.030), which has no page.

## Sources

- Jeroen Demeyer, *Recursively enumerable sets of polynomials over a finite field are Diophantine*, Inventiones Mathematicae 170 (2007), no. 3, 655–670, https://doi.org/10.1007/s00222-007-0078-6; read in the author's open-access copy of the journal version at https://biblio.ugent.be/publication/389620/file/1136560.pdf: the abstract and introduction, Section 5 (the theorem stated here, with the language $\{+, \cdot, 0, 1, \alpha, Z\}$ and the pairing function) and Theorem 11 of Section 6, in the journal's numbering.
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; read as arXiv:1309.0441v1: Section 5.2 (Function fields) of arXiv:1309.0441v1, which states that listable subsets of $\mathbb{F}_q[t]$ are Diophantine, crediting the paper above.
