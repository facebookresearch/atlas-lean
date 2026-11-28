# Nullstellensatz refutations over $\mathbb Z_m$ with the Impagliazzo–Segerlind size

Over the modular ring $\mathbb Z_m$ (for any integer $m>1$, with no primality assumption), Nullstellensatz refutations use the same Boolean-axiom identity and degree as the [Nullstellensatz proof system](../../algebraic-and-semialgebraic-proof-systems/nullstellensatz-proof-system.md) over a field, measured by the Impagliazzo–Segerlind size: the number of monomials appearing in $p_1,\dots,p_k$ and $f_1,\dots,f_k$.

Take the Nullstellensatz refutation identity $\sum_{i=1}^k p_if_i+\sum_{j=1}^n r_j(x_j^2-x_j)=1$ and its degree from [Nullstellensatz proof system](../../algebraic-and-semialgebraic-proof-systems/nullstellensatz-proof-system.md), extended here to polynomials $f_1,\dots,f_k,p_1,\dots,p_k,r_1,\dots,r_n$ over the ring $\mathbb Z_m$ with no assumption on $m$. Its **Impagliazzo–Segerlind size** is the number of monomials appearing in $p_1,\dots,p_k$ and $f_1,\dots,f_k$.

## Expansion

Over a field, Hilbert's weak Nullstellensatz guarantees completeness; over $\mathbb Z_m$ for composite $m$, refutations are still sound (the Boolean-axiom terms $x_j^2-x_j$ ensure no common $0/1$ root exists) though the system need not be complete. Nullstellensatz refutations over $\mathbb Z_m$ with this size are what [reductions from formulas to polynomial systems](reductions-to-polynomial-systems.md) assume, and constant-depth Frege with counting axioms [polynomially simulates them](counting-axioms-simulate-nullstellensatz.md).

## Depends on

- [Nullstellensatz proof system](../../algebraic-and-semialgebraic-proof-systems/nullstellensatz-proof-system.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 2.1, *Nullstellensatz Refutations*, Definition 6 and the definitions of degree and size over $\mathbb Z_m$ after it).
