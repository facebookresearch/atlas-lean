# Kohen's linear representation step modulo $p$

Let $p$ be a prime, let $P$ be a Laurent
polynomial in $r$ variables with integer coefficients, and write $\deg P$ for the largest absolute
value of an exponent of a single variable in a monomial occurring in $P$ ($0$ if $P = 0$). Let $m$
be a natural number with $\deg P \le m + 1$. Write $T = [-m, m]^r \subseteq \mathbb{Z}^r$ and
$[x^e]F$ for the coefficient of $x^e$ in a Laurent polynomial $F$. Then for every natural number
$k < p$, every natural number $n$ and every $i \in T$,

$$[x^{-i}]P^{pn+k} \equiv \sum_{j \in T} [x^{pj - i}]P^k \cdot [x^{-j}]P^n \pmod{p}.$$

With Kohen's $a^n_i = [x^{-i}]P^n$, $\gamma(k) = (a^k_{i-pj})_{i,j \in T}$ and
$V(n) = (a^n_i)_{i \in T}$, this is the entrywise form of $\gamma(k) V(n) = V(pn + k)$ over
$\mathbb{F}_p$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Lemma 9 (`jis-2026-26.4.2-lem-9`).
