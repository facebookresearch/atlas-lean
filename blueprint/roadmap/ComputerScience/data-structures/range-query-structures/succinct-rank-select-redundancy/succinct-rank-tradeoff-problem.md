# Succinct rank with a probe budget

Given a bit array $A[1..n]$, a *succinct rank structure with redundancy $r$* stores $n + r$ bits in cells of $w$ bits so that $\mathrm{Rank}(k) = \sum_{i \le k} A[i]$ can be answered by probing at most $t$ cells, with arbitrary free computation (cell-probe model); $\mathrm{Select}(x)$ asks for the $k$ with $\mathrm{Rank}(k-1) < x \le \mathrm{Rank}(k)$. The question is the optimal redundancy $r(n, w, t)$ as a function of the probe budget $t$.

## Depends on

- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)

## Sources

- Mihai Pătraşcu, Emanuele Viola, "Cell-Probe Lower Bounds for Succinct Partial Sums", SODA (2010).
- Mihai Pătraşcu, "Succincter", FOCS (2008).
