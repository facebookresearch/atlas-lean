# Passing from $P$ to $\tilde P$ modulo $p^a$

Let $p$ be a prime, let $a \ge 1$ and $\ell$
be natural numbers, and let $P$ and $\tilde P$ be Laurent polynomials in $r$ variables with
integer coefficients such that $P^{p^{a-1}} \equiv \tilde P(x^{p^\ell}) \pmod{p^a}$
coefficientwise, where $\tilde P(x^q)$ is obtained from $\tilde P$ by replacing each monomial
$x^e$ with $x^{qe}$. Write $\operatorname{ct}[F]$ for the constant term of a Laurent polynomial
$F$ and $\Lambda_q$ for Kohen's operator, which keeps the terms whose exponents are all divisible
by $q$ and replaces $x^{qj}$ by $x^j$. Then for every Laurent polynomial $Q$ in $r$ variables
with integer coefficients and all natural numbers $n$ and $k$,
$\operatorname{ct}[P^{p^{a-1} n + k} Q] \equiv
\operatorname{ct}[\tilde P^n \Lambda_{p^\ell}(P^k Q)] \pmod{p^a}$.

The statement holds for every natural number $k$; the paper restricts to $k < p^{a-1}$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Proposition 23 (`jis-2026-26.4.2-prop-23`).
