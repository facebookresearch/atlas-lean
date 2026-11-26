# Ancestral sampling has the chain joint as its law

Let $c$ be a chain of conditional distributions $p_k(\cdot \mid x_0, \dots, x_{k-1})$ on a finite set $\alpha$. For every $n$ and every $x \in \alpha^n$, the probability that ancestral sampling (draw $x_0, x_1, \dots, x_{n-1}$ in order, each from its conditional distribution given the earlier values) produces $x$ equals the chain-rule joint $\prod_{k < n} p_k(x_k \mid x_0, \dots, x_{k-1})$.
