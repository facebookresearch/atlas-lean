# Nullstellensatz refutations

A Nullstellensatz refutation of polynomials $f_1,\dots,f_k$ in $x_1,\dots,x_n$ is a list of polynomials $p_1,\dots,p_k,r_1,\dots,r_n$ with $\sum_ip_if_i+\sum_jr_j(x_j^2-x_j)=1$, certifying that the $f_i$ have no common $0/1$ root; its size is the number of monomials in the $p_i$ and the $f_i$.

Let $f_1,\dots,f_k$ be polynomials in $x_1,\dots,x_n$ over a field, or more generally over a ring such as $\mathbb Z_m$. A *Nullstellensatz refutation* of $f_1,\dots,f_k$ is a list $p_1,\dots,p_k,r_1,\dots,r_n$ of polynomials with

$$
\sum_{i=1}^k p_if_i+\sum_{j=1}^n r_j\,(x_j^2-x_j)=1 .
$$

A *Nullstellensatz derivation* of $q$ from $f_1,\dots,f_k$ is the same with right-hand side $q$. The *degree* of the refutation is the maximum degree of the polynomials $p_if_i$ and $r_j(x_j^2-x_j)$, and its *size* is the number of monomials appearing in $p_1,\dots,p_k$ and $f_1,\dots,f_k$. The terms $x_j^2-x_j$ restrict attention to $0/1$ roots, so a refutation exists only when the $f_i$ have no common $0/1$ root.

## Expansion

Over a field, Hilbert's weak Nullstellensatz guarantees that every system with no common $0/1$ root has such a refutation; over a ring such as $\mathbb Z_m$ refutations can still be defined but the system need not be complete, and no assumption on $m$ is made. Nullstellensatz refutations over $\mathbb Z_m$ are what [reductions from formulas to polynomial systems](reductions-to-polynomial-systems.md) assume, and constant-depth Frege with counting axioms [polynomially simulates them](counting-axioms-simulate-nullstellensatz.md).

## Depends on

None.

## Proof depends on

None.

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 2.1, *Nullstellensatz Refutations*, Definition 6 and the definitions of degree and size after it).
