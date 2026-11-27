# Sums-of-Squares simulates Sherali-Adams and Polynomial Calculus

A degree-$d$, size-$s$ Sherali-Adams derivation converts into a degree-$2d$ Sums-of-Squares derivation of size $\mathrm{poly}(s)$, and for a system of real polynomial equations over Boolean variables a degree-$d$, size-$S$ Polynomial Calculus refutation over $\mathbb{R}$ converts into a degree-$2d$ Sums-of-Squares refutation of size $\mathrm{poly}(S)$.

**Theorem.**

1. If $p(x) \ge 0$ has a Sherali-Adams derivation of degree $d$ and size $s$ from a set $\mathcal{P}$ of polynomial inequalities, then it has a Sums-of-Squares derivation from $\mathcal{P}$ of degree $2d$ and size $\mathrm{poly}(s)$.
2. (Berkholz.) Let $\mathcal{F} = \{f_1 = 0, \dots, f_m = 0\}$ be a system of polynomial equations with $f_i \in \mathbb{R}[x_1, \dots, x_n]$, with the Boolean axioms $x_j^2 - x_j = 0$ present in both systems. If $\mathcal{F}$ has a Polynomial Calculus refutation over $\mathbb{R}$ of degree $d$ and size $S$, then it has a Sums-of-Squares refutation of degree $2d$ and size $\mathrm{poly}(S)$. Size is the total bit size of the polynomials written as sums of monomials, as in the source; the statement also holds with twin variables.

Here a degree-$d$ Sums-of-Squares derivation of $p \ge c_0$ writes $p - c_0$ as $q_0 + \sum_i p_i q_i$, where $q_0$ is a sum of squares, each $p_i$ is a hypothesis or a Boolean axiom and each $q_i$ is a sum of squares (in effect an arbitrary polynomial for an equality constraint), all terms of degree at most $d$. Part 2 needs the real field: over $\mathbb{F}_2$, Polynomial Calculus refutes every unsatisfiable 3-XOR system in constant degree and polynomial size by Gaussian elimination, while random 3-XOR instances of constant density need Sums-of-Squares degree linear in $n$ ([Sum-of-Squares lower bounds for refuting random CSPs](../sum-of-squares-average-case-lower-bounds/random-csp-sum-of-squares-lower-bound.md)).

## Proof sketch

For part 1 it suffices to treat one term $p_i(x) J_{S,T}(x)$ with a nonnegative junta: the polynomial $p_i(x) (J_{S,T}(x))^2$ is an SoS term of degree at most $2d$, and it is multilinearized in SoS without raising the degree, which recovers $p_i J_{S,T}$. Sums-of-Squares is strictly stronger: the pigeonhole principle $\mathrm{PHP}^n_{n-1}$ has degree-$4$ polynomial-size SoS refutations but needs SA degree at least $n - 1$ (Dantchev, Martin and Rhodes). Sherali-Adams is strictly stronger than Nullstellensatz, since pebbling contradictions need Nullstellensatz degree $\Omega(n/\log n)$ but have small-degree SA refutations, while PC and SA are incomparable; part 2 shows that the cancellations of a dynamic PC refutation are captured by one static SoS identity.

## Depends on

- [Sherali-Adams proof system](sherali-adams-proof-system.md)
- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)
- [Polynomial calculus](../polynomial-calculus.md)

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086; numbering of ECCC report TR19-106, revision 3, 2020 (Lemma 3.64, Definition 3.54, Claims 3.58 and 3.60, Figure 3.5; Theorem 3.65 restates part 2 without naming the field).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Theorem 1.1, Section 2 and the remark in Section 2.3; primary source of part 2).
