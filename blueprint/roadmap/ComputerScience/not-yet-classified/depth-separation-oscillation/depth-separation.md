# Depth separation for ReLU networks

Let $L \ge 2$ and let $f_k$ be the $k$-fold iterate of the tent map $t(x) = 2\,\mathrm{relu}(x) - 4\,\mathrm{relu}(x - 1/2) + 2\,\mathrm{relu}(x - 1)$. Then:

- a ReLU network of depth $2(L^2 + 2)$ computes $f_{L^2 + 2}(x)$ exactly for every real $x$;
- every ReLU network $N$ with one input and one output, $1 \le M \le L$ layers, positive widths $d_1, \dots, d_{M-1}$ and total width $\sum_{i=1}^M d_i \le 2^L$ satisfies

    $$\int_0^1 \bigl|f_{L^2+2}(x) - N(x)\bigr|\,dx \ge \frac{1}{32}.$$
