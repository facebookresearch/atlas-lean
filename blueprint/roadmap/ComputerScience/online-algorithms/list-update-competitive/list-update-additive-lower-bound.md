# List Update additive Lower Bound

For a nonempty duplicate-free list $M$ of $\ell$ items, list update over $M$ has additive lower bound $2\ell/(\ell + 1)$: for every feasible deterministic strategy, every $0 \le c < 2\ell/(\ell+1)$ and every $b \ge 0$, some legal request sequence has $c \cdot \mathrm{OPT} + b < \mathrm{ALG}$ (the Karp–Raghavan and Irani bound). Distinctness matters: on $[x, x]$, keeping the list unchanged costs one per request, as does the optimum.
