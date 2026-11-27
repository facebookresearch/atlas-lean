# Presburger arithmetic with scalar multiplications

For a real number $\alpha$, $\alpha$-Presburger arithmetic is the set of true sentences quantifying over blocks of integer variables whose matrix is a Boolean combination of linear inequalities with coefficients in $\mathbb Z[\alpha]$; for rational $\alpha$ it is ordinary Presburger arithmetic.

**Definition.** Let $\alpha$ be a real number. An *$\alpha$-Presburger sentence* ($\alpha$-PA sentence) is a statement

$$
Q_1 \mathbf x_1 \in \mathbb Z^{n_1}\ \cdots\ Q_r \mathbf x_r \in \mathbb Z^{n_r}\ \ \Phi(\mathbf x_1, \ldots, \mathbf x_r),
$$

where $Q_1, \ldots, Q_r \in \{\forall, \exists\}$ alternate, $\mathbf x_1, \ldots, \mathbf x_r$ are blocks of integer variables, and $\Phi$ is a Boolean combination of linear inequalities in the variables with coefficients and constant terms in $\mathbb Z[\alpha]$. Writing $\exists^{n_1}\forall^{n_2}\cdots$ for the shape of the prefix, an $\exists^k\forall^k\exists^k\forall^k$ sentence has four alternating blocks of $k$ variables each, the first existential. More generally, for a subfield $K$ of $\mathbb R$, a *$K$-PA sentence* has the same form with coefficients and constants in $K$. The decision problem is to determine, given such a sentence, whether it is true in $\mathbb Z$. A real algebraic $\alpha$ is given by its defining polynomial over $\mathbb Z$ of degree $d$ and a rational interval isolating it, and is *quadratic* if $d = 2$; elements of $\mathbb Z[\alpha]$ are written $c_0 + c_1\alpha + \cdots + c_{d-1}\alpha^{d-1}$ with integer $c_i$ in binary.

When $\alpha \in \mathbb Q$, deciding $\alpha$-PA sentences is equivalent to deciding Presburger arithmetic, the first-order theory of $(\mathbb Z, <, +)$, which is decidable (see [quantifier elimination for Presburger arithmetic](../../quantifier-elimination-for-presburger-arithmetic.md)). An $\alpha$-PA sentence is true iff it belongs to the first-order theory of $(\mathbb R, <, +, \mathbb Z, x \mapsto \alpha x)$.

## Depends on

None.

## Proof depends on

None.

## Expansion

For quadratic irrational $\alpha$ the theory is still decidable (Theorem 3.1 of the source, from Hieronymi's decidability of $(\mathbb R, <, +, \mathbb Z, x \mapsto \alpha x)$), through the Ostrowski numeration system attached to the continued fraction of $\alpha$, which makes $\alpha$-PA definable sets recognizable by finite automata (Corollary 4.11), but with very high complexity (Theorems 1.2 to 1.4). For non-quadratic algebraic $\alpha$ it is undecidable.

## Sources

- P. Hieronymi, D. Nguyen and I. Pak, "Presburger Arithmetic with algebraic scalar multiplications", *Logical Methods in Computer Science* 17(3), 2021, article 4, pp. 4:1–4:34, <https://doi.org/10.46298/lmcs-17(3:4)2021>; numbers from arXiv:1805.03624v7, <https://arxiv.org/abs/1805.03624v7>: Section 1.1 (definition (1.1) of $\alpha$-PA sentences and the encoding of $\alpha$), Section 7 (definition (7.1) of $K$-PA sentences), Theorem 3.1 and Corollary 4.11.
