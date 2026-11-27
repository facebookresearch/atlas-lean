# Sums-of-Squares simulates Sherali-Adams and Polynomial Calculus

A degree-$d$, size-$s$ Sherali-Adams derivation converts into a degree-$2d$ Sums-of-Squares derivation of size $\mathrm{poly}(s)$, and a degree-$d$, size-$s$ Polynomial Calculus refutation converts into a degree-$2d$ Sums-of-Squares refutation of size $\mathrm{poly}(s)$; the converses fail.

**Theorem.**

1. If $p(x) \ge 0$ has a Sherali-Adams derivation of degree $d$ and size $s$ from a set $\mathcal{P}$ of polynomial inequalities, then it has a Sums-of-Squares derivation from $\mathcal{P}$ of degree $2d$ and size $\mathrm{poly}(s)$.
2. (Berkholz.) For any unsatisfiable set $\mathcal{P}$, if there is a Polynomial Calculus refutation of $\mathcal{P}$ of degree $d$ and size $s$, then there is a Sums-of-Squares refutation of $\mathcal{P}$ of degree $2d$ and size $\mathrm{poly}(s)$.

Here a degree-$d$ Sums-of-Squares derivation of $p \ge c_0$ writes $p - c_0$ as a sum of hypotheses and Boolean axioms multiplied by sums of squares (arbitrary polynomials for equality constraints), all terms of degree at most $d$.

## Expansion

For part 1 it suffices to treat one term $p_i(x) J_{S,T}(x)$ with a nonnegative junta: the polynomial $p_i(x) (J_{S,T}(x))^2$ is an SoS term of degree at most $2d$, and it is multilinearized in SoS without raising the degree, which recovers $p_i J_{S,T}$. Sums-of-Squares is strictly stronger: the pigeonhole principle $\mathrm{PHP}^n_{n-1}$ has degree-$4$ polynomial-size SoS refutations but needs SA degree at least $n - 1$ (Dantchev, Martin and Rhodes). Sherali-Adams is strictly stronger than Nullstellensatz, since pebbling contradictions need Nullstellensatz degree $\Omega(n/\log n)$ but have small-degree SA refutations, while PC and SA are incomparable; part 2 shows that the cancellations of a dynamic PC refutation are captured by one static SoS identity.

## Depends on

- [Sherali-Adams proof system](sherali-adams-proof-system.md)

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086 (Lemma 3.64, Theorem 3.65, Definition 3.54, Claims 3.58 and 3.60, Figure 3.5).
