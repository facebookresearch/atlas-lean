# Kohen's linear representation step modulo $p^a$

Let $p$ be a prime, let $a$ be a natural
number, and let $\tilde P$ be a Laurent polynomial in $r$ variables with integer coefficients such
that $\tilde P^p \equiv \tilde P(x^p) \pmod{p^a}$ coefficientwise, where $\tilde P(x^p)$ is
obtained from $\tilde P$ by replacing each monomial $x^e$ with $x^{pe}$. Write $\deg \tilde P$ for
the largest absolute value of an exponent of a single variable in a monomial occurring in
$\tilde P$ ($0$ if $\tilde P = 0$). Let $m$ be a natural number with $\deg \tilde P \le m + 1$,
and write $T = [-m, m]^r \subseteq \mathbb{Z}^r$ and $[x^e]F$ for the coefficient of $x^e$ in a
Laurent polynomial $F$. Then for every natural number $k < p$, every natural number $n$ and every
$i \in T$,

$$
[x^{-i}]\tilde P^{pn+k} \equiv
\sum_{j \in T} [x^{pj - i}]\tilde P^k \cdot [x^{-j}]\tilde P^n \pmod{p^a}.
$$

This is the entrywise form of Kohen's step $\tilde\gamma(k) \tilde V(n) = \tilde V(pn + k)$ over
$\mathbb{Z}/p^a\mathbb{Z}$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Lemma 28 (`jis-2026-26.4.2-lem-28`).
