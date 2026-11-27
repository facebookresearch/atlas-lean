# Elastic hashing layout and batch insertion rule

*Elastic hashing* partitions the $n$ slots into disjoint subarrays $A_1, A_2, \dots, A_{\lceil \log_2 n \rceil}$ with $|A_{i+1}| = |A_i|/2 \pm 1$. Each key $x$ has independent uniform probe positions $h_{i,1}(x), h_{i,2}(x), \dots \in A_i$ for every $i$, serialized by an injection $\phi$ of index pairs with $\phi(i, j) = O(i j^2)$. The $n - \lfloor \delta n \rfloor$ insertions are processed in batches $\mathcal{B}_0, \mathcal{B}_1, \dots$: batch $\mathcal{B}_0$ fills $A_1$ until it holds $\lceil 3|A_1|/4 \rceil$ keys, and during batch $\mathcal{B}_i$ ($i \ge 1$) keys are placed in $A_i \cup A_{i+1}$ until $A_i$ holds exactly $|A_i| - \lfloor \delta |A_i|/2 \rfloor$ keys and $A_{i+1}$ holds exactly $\lceil 3|A_{i+1}|/4 \rceil$ keys, which fixes the size of $\mathcal{B}_i$ (Eq. (1)); the final batch may stop early when the insertions run out. If $A_i$ has a free fraction $\varepsilon_1 > \delta/2$ and $A_{i+1}$ a free fraction $\varepsilon_2 > 1/4$, the key tries $f(\varepsilon_1) = c \min(\log^2 \varepsilon_1^{-1}, \log \delta^{-1})$ probes in $A_i$ (for a suitable constant $c$) and otherwise falls through to probes in $A_{i+1}$; if $\varepsilon_1 \le \delta/2$ it uses $A_{i+1}$; if $\varepsilon_2 \le 1/4$ it probes $A_i$ greedily. The rule is non-greedy: a key may examine probes far down its sequence and then use an earlier one.

## Depends on

- [Open-addressing insertion without reordering](oa-without-reordering-model.md)
- [An injection of index pairs with cost $O(i j^2)$](pairing-injection-with-quadratic-weight.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
