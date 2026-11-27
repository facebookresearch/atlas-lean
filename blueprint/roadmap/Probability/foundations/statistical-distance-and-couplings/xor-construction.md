# XOR construction of two distributions

Let $p_0, p_1$ be distributions on a finite set $X$, $k \ge 1$ and $c \in \{0,1\}$. The *XOR construction* $\mathrm{XOR}_k(p_0, p_1; c)$ is the distribution on $X^k$ obtained by drawing a selector string $b \in \{0,1\}^k$ uniformly among the strings with $b_1 \oplus \dots \oplus b_k = c$ and then drawing $x_i \sim p_{b_i}$ independently for $i = 1, \dots, k$. It can be sampled from uniform bits by drawing $b_1, \dots, b_{k-1}$ uniformly and setting $b_k = c \oplus b_1 \oplus \dots \oplus b_{k-1}$, so if $p_0, p_1$ are images of uniform seeds under maps $f_0, f_1$ then so is the construction.

## Sources

- A. Sahai and S. Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
