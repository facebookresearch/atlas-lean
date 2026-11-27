# Nullstellensatz proofs and degree

A *Nullstellensatz proof* of a polynomial $q$ from input polynomials $f_1,\dots,f_m$ over a commutative ring is a family of multipliers $g_1,\dots,g_m$ with $\sum_i g_i f_i = q$; it is a *refutation* when $q = 1$. Its *degree* is $\max_i \deg(g_i f_i)$ and its *size* the total number of monomials of the products $g_i f_i$ written out as linear combinations of monomials. A system is refutable in degree $d$ if it has a refutation of degree at most $d$. Proofs are sound: $q$ vanishes at every common zero of the inputs, so a refutable system (over a nontrivial ring) has no common zero.

## Depends on

- [Boolean axioms and CNF arithmetization](boolean-axioms-and-cnf-arithmetization.md)

## Sources

- P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi and P. Pudlák, "Lower Bounds on Hilbert's Nullstellensatz and Propositional Proofs", Proceedings of the London Mathematical Society 73(1), 1–26, 1996.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.5.1 (refutations (7.15), size and degree).
