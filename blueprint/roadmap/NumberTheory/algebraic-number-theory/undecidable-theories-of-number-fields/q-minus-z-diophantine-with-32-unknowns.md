# The non-integers are Diophantine over the rationals with 32 unknowns, so ∀⁹∃³² sentences over the rationals are undecidable

There is an integer polynomial $P(t, x_1, \dots, x_{32})$ such that a rational $t$ is not an integer exactly when $P(t, x_1, \dots, x_{32}) = 0$ has a rational solution; consequently no algorithm decides the truth over $\mathbb{Q}$ of sentences $\forall x_1 \cdots \forall x_9\, \exists y_1 \cdots \exists y_{32}\, [f = 0]$.

For a prefix of quantifiers $\rho_1 x_1 \cdots \rho_k x_k$ with each $\rho_i \in \{\forall, \exists\}$, the decision problem "$\rho_1 \cdots \rho_k$ over $\mathbb{Q}$" asks, for a polynomial $f \in \mathbb{Z}[x_1, \dots, x_k]$, whether the sentence $\rho_1 x_1 \cdots \rho_k x_k\, [f(x_1, \dots, x_k) = 0]$ holds with all variables ranging over $\mathbb{Q}$. Then (source):

1. $\mathbb{Q} \setminus \mathbb{Z}$ has a Diophantine representation over $\mathbb{Q}$ with $32$ unknowns: there is $P \in \mathbb{Z}[t, x_1, \dots, x_{32}]$, constructible explicitly with $\deg P < 2.1 \times 10^{11}$, such that for every $t \in \mathbb{Q}$

$$
t \notin \mathbb{Z} \iff \exists x_1 \cdots \exists x_{32} \in \mathbb{Q}\ [P(t, x_1, \dots, x_{32}) = 0]
$$

(Theorem 1.1); equivalently, $t \in \mathbb{Z}$ if and only if $P(t, x_1, \dots, x_{32}) \ne 0$ for all rational $x_1, \dots, x_{32}$;

2. $\forall^9 \exists^{32}$ over $\mathbb{Q}$ is undecidable: no algorithm decides, for $f \in \mathbb{Z}[x_1, \dots, x_9, y_1, \dots, y_{32}]$, whether $\forall x_1 \cdots \forall x_9\, \exists y_1 \cdots \exists y_{32}\, [f = 0]$ holds over $\mathbb{Q}$; also $\exists^9 \forall^{32} \exists$ and $\exists^{10} \forall^{31} \exists$ over $\mathbb{Q}$ are undecidable (Theorem 1.3).

Julia Robinson defined $\mathbb{Z}$ in $\mathbb{Q}$ by a first-order formula and Poonen by a $\forall^2 \exists^7$ formula; Koenigsmann proved that $\mathbb{Q} \setminus \mathbb{Z}$ is Diophantine over $\mathbb{Q}$, with between 400 and 500 unknowns, and Daans reduced the number to $50$, as the source recalls.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Clause 1 starts from Daans' simplification of Koenigsmann's universal definition of $\mathbb{Z}$ in $\mathbb{Q}$ and uses a new relation-combining theorem for Diophantine representations over $\mathbb{Q}$, an analogue of the relation-combining theorem of Matiyasevich and Robinson (Theorem 1.2 of the source). For clause 2 the source uses Sun's representation of every recursively enumerable set $\mathcal{A} \subseteq \mathbb{N}$ by a polynomial in $9$ integer unknowns, one of them nonnegative (Lemma 4.2, from Theorem 1.1 of Sun's paper on Hilbert's tenth problem). Universal quantifiers over $\mathbb{Q}$ guarded by clause 1 range over $\mathbb{Z}$, nonnegativity is expressed by Euler's four-squares representation of nonnegative rationals (Lemma 4.1), and a non-recursive r.e. set then gives a $\forall^9 \exists^{32}$ problem without a decision procedure. A good expansion links pages for Daans' universal definition of $\mathbb{Z}$ in $\mathbb{Q}$, for the relation-combining theorem over $\mathbb{Q}$ (Theorem 1.2 of the source), for Sun's representation of recursively enumerable sets, and for Lemmas 4.1 and 4.2 of the source.

## Sources

- G.-R. Zhang and Z.-W. Sun, "$\mathbb{Q} \setminus \mathbb{Z}$ is diophantine over $\mathbb{Q}$ with 32 unknowns", Bulletin of the Polish Academy of Sciences Mathematics 70 (2022), no. 2, 93–106, https://doi.org/10.4064/ba221231-19-3; read in arXiv:2104.02520v4 (the introduction, Theorems 1.1, 1.2 and 1.3 and Lemmas 4.1 and 4.2 of arXiv:2104.02520v4, in that version's numbering).
