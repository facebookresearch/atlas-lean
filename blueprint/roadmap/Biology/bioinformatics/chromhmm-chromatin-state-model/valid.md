# Valid ChromHMM parameters

[ChromHMM parameters](params.md) are valid if

- $\pi(s) > 0$ for every $s$ and $\sum_s \pi(s) = 1$;
- $a(s, s') > 0$ for all $s, s'$ and $\sum_{s'} a(s, s') = 1$ for every $s$;
- $0 < p_{s,j} < 1$ for all $s, j$.
