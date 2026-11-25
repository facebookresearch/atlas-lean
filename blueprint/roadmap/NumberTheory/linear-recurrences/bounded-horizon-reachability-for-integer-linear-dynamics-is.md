# Bounded-horizon reachability for integer linear dynamics is polynomial

Let $M \in \mathbb{Z}^{k \times k}$ with $k \ge 1$, let $s, e \in \mathbb{Z}^k$, and let
$u_n = e^{\mathsf T} M^n s$. Write $\alpha = \max(1, \max_{i,j} \lvert M_{ij} \rvert)$ and
$\beta = \max(1, \max_i \lvert s_i \rvert)$ (the maxima with $1$ keep the logarithms below defined
when $M$ or $s$ is zero). Then:

1. for every $n \ge 0$, every entry of $M^n s$ has absolute value at most $(k\alpha)^n \beta$, hence binary
   bit-length, not counting a sign bit, at most $n \log_2(k\alpha) + \log_2 \beta + 1$;
2. given the horizon $N \ge 0$ in unary, computing $M s, M^2 s, \dots, M^N s$ by repeated multiplication
   decides whether $u_n = 0$ for some $n \le N$ in time polynomial in $N$, $k$ and the bit-length of
   $M$, $s$, $e$, under the bit-cost model;
3. given $N \ge 0$ in binary, repeated squaring computes $u_N$ (for $N = 0$, directly $u_0 = e^{\mathsf T} s$) with $O(k + k^3 \log(N+1))$
   arithmetic operations on integers, and, for a modulus $p \ge 2$, computes $u_N \bmod p$ in time polynomial in $\log(N+1)$, $k$, $\log p$ and
   the bit-length of $M$, $s$, $e$. Exact output is not polynomial in $\log N$: for $M = (2)$ and
   $s = e = (1)$, $u_N = 2^N$ has $N + 1$ bits. Deciding whether $u_n = 0$ for some $n \le N$ is not
   claimed to be polynomial in $\log N$.

## Expansion

This node states a precise result. A good expansion adds a page for
the pending prerequisite below, linked under the dependency sections.

- Statement prerequisite: the bit-cost and arithmetic-operation cost models, stated separately.

## Depends on

- [Skolem, positivity and bounded reachability problems for LRS](skolem-positivity-and-bounded-reachability-problems-for-lrs.md)

## Sources

- J. Worrell, *The Skolem landscape* (invited talk), ICALP 2023, LIPIcs 261, 5:1–5:2.
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.5> Background reference.
