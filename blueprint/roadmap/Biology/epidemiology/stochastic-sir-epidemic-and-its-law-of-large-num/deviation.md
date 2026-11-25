# Deviation of the scaled chain from a deterministic path

For a natural number $N$, paths $S, I, R \colon \mathbb{R} \to \mathbb{N}$, real functions $s$,
$i$, $r$ and a time $t$, the deviation is the $\ell^1$ distance at time $t$ between the scaled
counts $(S, I, R)/N$ and $(s, i, r)$:

$$D(t) = \left|S(t)/N - s(t)\right| + \left|I(t)/N - i(t)\right| + \left|R(t)/N - r(t)\right|.$$

It is meant for $N \ge 1$; for $N = 0$ the convention $x/0 = 0$ gives
$D(t) = |s(t)| + |i(t)| + |r(t)|$.
