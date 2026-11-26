# Nullstellensatz proofs and degree

A *Nullstellensatz proof* of a polynomial $q$ from input polynomials $f_1,\dots,f_m$ over a commutative ring is a family of multipliers $g_1,\dots,g_m$ with $\sum_i g_i f_i = q$; it is a *refutation* when $q = 1$. Its *degree* is $\max_i \deg(g_i f_i)$ and its *size* the total number of monomials of the $g_i$. A system is refutable in degree $d$ if it has a refutation of degree at most $d$. Proofs are sound: $q$ vanishes at every common zero of the inputs, so a refutable system (over a nontrivial ring) has no common zero.

## Depends on

- [Boolean axioms and CNF arithmetization](boolean-axioms-and-cnf-arithmetization.md)
- [Combinatorial Nullstellensatz, Theorem 1.1](../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-eq-sum-mul-of-vanishing.md)

## Sources

- P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi and P. Pudlák, "Lower Bounds on Hilbert's Nullstellensatz and Propositional Proofs", Proceedings of the London Mathematical Society 73(1), 1–26, 1996.
