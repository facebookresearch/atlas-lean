# Shallow ReLU networks miss the deep tent iterate

Let $L \ge 2$ and let $N$ be a ReLU network with $M$ layers, $1 \le M \le L$, input and output width $1$, positive widths $d_0, \dots, d_{M-1}$ and total width $\sum_{i=1}^{M} d_i \le 2^L$. Then $\int_0^1 |t^{(L^2+2)}(x) - N(x)|\,dx \ge 1/32$, where $t^{(L^2+2)}$ is the $(L^2+2)$-fold iterate of the tent map.
