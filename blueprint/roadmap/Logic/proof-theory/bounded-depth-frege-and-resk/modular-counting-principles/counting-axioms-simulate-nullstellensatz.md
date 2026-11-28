# Counting axioms polynomially simulate Nullstellensatz

If a formula $\Gamma$ reduces in depth $d$ and size $T$ to a polynomial system over $\mathbb Z_m$ with a size-$S$ Nullstellensatz refutation, then $\Gamma$ has a depth-$O(d)$ refutation of size $O(S^{2m}T)$ in Frege with counting axioms modulo $m$.

[Nullstellensatz refutations over $\mathbb Z_m$ with the Impagliazzo–Segerlind size](nullstellensatz-refutations.md) are taken with no assumption on $m$, where the size is the number of monomials appearing in $p_1,\dots,p_k$ and $f_1,\dots,f_k$.

**Theorem.** Let $m>1$ be an integer, $\Gamma(\vec x)$ a propositional formula and $F$ a system of polynomials over $\mathbb Z_m$ such that $\Gamma$ [reduces](reductions-to-polynomial-systems.md) to $F$ in depth $d$ and size $T$. If $F$ has a Nullstellensatz refutation of size $S$, then $\Gamma(\vec x)$ has a depth-$O(d)$ refutation in Frege with [counting axioms modulo $m$](counting-axioms-modulo-m.md) of size $O(S^{2m}T)$.

## Expansion

Expand $\sum_i\bar p_i\bar f_i$ without collecting terms: its monomial copies are the triples $(m_{c,I},m_{d,J},i)$ with $m_{c,I}$ a copy in $\bar p_i$ and $m_{d,J}$ a copy in $\bar f_i$, a set $V$ of size $O(S^2)$, with $\gamma_v=\bigwedge_{k\in I\cup J}x_k$ saying the copy is satisfied. Using the partitions supplied by the reduction and the identity $\sum_ip_if_i+\sum_jr_j(x_j^2-x_j)=1$ over $\mathbb Z_m$, the proof defines by small constant-depth formulas two partitions of the satisfied copies: one covering them exactly, and one covering them together with $m-1$ extra points. A contradictory-partitions tautology $\mathrm{CP}$ saying both cannot exist has constant-depth size $O(N^m)$ proofs from the counting axioms, and instantiating it costs $O(S^{2m}+T)$ symbols. The simulation shows that Nullstellensatz *degree* lower bounds are necessary for size lower bounds on constant-depth Frege with counting axioms, since low-degree refutations are small. Combined with an earlier separation of the authors it gives the first superpolynomial size separation between Nullstellensatz and polynomial calculus refutations.

## Depends on

- [Counting axioms modulo m](counting-axioms-modulo-m.md)
- [Nullstellensatz refutations over $\mathbb Z_m$ with the Impagliazzo–Segerlind size](nullstellensatz-refutations.md)
- [Reductions from formulas to polynomial systems](reductions-to-polynomial-systems.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (abstract and Section 1; Section 2.1, *Nullstellensatz Refutations*, Definition 6; Section 3, contradictory partitions; Section 4.2, Theorem 1, the simulation theorem).
