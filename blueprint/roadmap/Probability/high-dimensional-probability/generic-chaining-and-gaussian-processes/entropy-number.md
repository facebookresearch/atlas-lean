# Entropy numbers

$$e_n(T) = \inf\big\{\sup_{t \in T} d(t, T_n) : T_n \subseteq T,\ \operatorname{card} T_n \le N_n\big\},$$

the smallest radius $r$ such that $T$ is covered by at most $N_n$ balls of radius $r$ centred in
$T$ (Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, (2.36)). The
value lies in $[0, \infty]$. Operator theory writes $e_{2^n}$ for Talagrand's $e_n$; in terms of
covering numbers, $e_n(T) \le \varepsilon$ roughly when $\log N(T, d, \varepsilon) \le 2^n \log 2$.

## Background

- [Entropy numbers from finite covers](entropy-number-le-of-is-cover.md): the comparison with covering
  numbers, which count the same covers.
