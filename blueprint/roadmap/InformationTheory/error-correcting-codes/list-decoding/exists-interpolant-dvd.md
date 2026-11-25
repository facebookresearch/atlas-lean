# Guruswami–Sudan list decoding

Let $\alpha_1, \dots, \alpha_n \in F$ be distinct, $y \in F^n$, and $w, D, r$ natural numbers such
that more than $n \cdot r(r+1)/2$ monomials $X^i Y^j$ (with $i, j \le D$) satisfy
$i + w j \le D$. There is one nonzero $Q \in F[X][Y]$ of [$(1, w)$-weighted degree](weighted-deg-le.md)
at most $D$, depending only on $\alpha$ and $y$, such that $Y - P(X)$ divides $Q$ for every
$P \in F[X]$ of degree at most $w$ with $P(\alpha_i) = y_i$ for $t$ indices $i$, where $D < t r$.
When $w \ge 1$, at most $\lfloor D / w \rfloor$ polynomials $P$ have $Y - P(X)$ dividing $Q$
([list size](card-le-div-of-dvd.md)).

With $w = k - 1$ this is the correctness of the Guruswami–Sudan algorithm (Algorithm 12.2.3 of
Guruswami, Rudra and Sudan) for any parameters $D, r$ satisfying the monomial-count hypothesis:
interpolate, then read off the factors $Y - P(X)$ of $Q$. That is, every
$P$ with $\deg P \le w$ and $t$ agreements, where $D < t r$, is found. Their choice
$D = \lceil \sqrt{(k-1) n r (r+1)} \rceil$ with $r$ large makes the agreement threshold $D / r$
drop to about $\sqrt{(k-1) n}$, so that Reed–Solomon codes of rate $R$ are decoded from up to a
$1 - \sqrt{R}$ fraction of errors (Theorem 12.2.12), in polynomial time.

## Informally uses

- [Guruswami–Sudan interpolation step](exists-interpolant.md): Step 1.
- [$Y - P(X)$ divides the interpolating polynomial](x-sub-c-dvd-of-agree.md): Steps 2 and 3, via Lemma 12.2.13.

## Sources

- V. Guruswami, M. Sudan, "Improved decoding of Reed–Solomon and algebraic-geometry codes", *IEEE Transactions on Information Theory* 45(6) (1999), 1757–1767.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Algorithm 12.2.3 and Theorem 12.2.12.
