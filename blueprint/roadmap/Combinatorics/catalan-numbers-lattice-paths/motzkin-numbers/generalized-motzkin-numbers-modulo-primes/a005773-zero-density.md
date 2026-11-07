# Zero density of A005773 modulo a prime

Let $p$ be a prime, let $T_m$ be the central
trinomial coefficient, the constant term of $(x^{-1} + 1 + x)^m$, and let $a_n$ be the constant
term of $(1 + x)(x^{-1} + 1 + x)^n$ (OEIS A005773). If $T_r \equiv 0 \pmod p$ for some $r < p$,
then the set of $n \in \mathbb{N}$ with $a_n \equiv 0 \pmod p$ has natural density $1$. If
instead $T_r \not\equiv 0 \pmod p$ for every $r < p$ and $p > 2$, let $N_1$ be the number of
$m < p - 1$ with $T_m \equiv -T_{p-1} T_{m+1} \pmod p$ and let $N_2$ be the number of
$m < p - 1$ with $T_m \equiv -T_{m+1} \pmod p$. Then that set has natural density
$D_0 = (N_1 + p N_2) / ((p - 1)(p + 1))$, and $D_0 \ge 1/(p - 1)$.

## Sources

- Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Proposition 8.
