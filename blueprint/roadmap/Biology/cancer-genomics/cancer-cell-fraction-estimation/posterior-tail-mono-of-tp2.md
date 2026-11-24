# Monotone likelihood ratio implies stochastically larger posteriors

Let $I$ be a finite index set, $\pi, L, L', c : I \to \mathbb{R}$ and $t$ real. Suppose that

- $\pi_i \ge 0$ for every $i$;
- $L_i L'_j \le L'_i L_j$ whenever $c_j \le c_i$ (the TP2 inequality);
- $\sum_i \pi_i L_i > 0$ and $\sum_i \pi_i L'_i > 0$.

Then $\mathrm{Tail}(\pi, L, c; t) \le \mathrm{Tail}(\pi, L', c; t)$, where $\mathrm{Tail}$ is the [posterior tail](tail-ratio.md).
