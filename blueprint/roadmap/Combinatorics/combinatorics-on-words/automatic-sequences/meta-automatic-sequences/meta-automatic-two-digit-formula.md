# Digit formula for $\mathcal{M}_2$

For a natural number $n$ and $k \ge 0$, let
$d_k = \lfloor n / 4^k \rfloor \bmod 4$ be the $k$-th base-$4$ digit of $n$, and write
$d_k = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$. Let $c_k = i_k + j_k$ if $k \equiv 0 \pmod 3$,
$c_k = j_k$ if $k \equiv 1 \pmod 3$, and $c_k = i_k$ if $k \equiv 2 \pmod 3$. Then the
meta-automatic sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = (c_0 + c_1 + \cdots + c_n) \bmod 2$.

The digits $d_k$ with $k > n$ vanish, so the sum runs over all base-$4$ digits of $n$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 25 (`jis-2026-26.4.1-thm-25`).
