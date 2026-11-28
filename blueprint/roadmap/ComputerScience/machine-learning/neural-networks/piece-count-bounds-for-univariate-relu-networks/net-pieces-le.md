# Piece-count bound for univariate ReLU networks

Let a ReLU network have $L \ge 1$ layers with widths $d_0, d_1, \dots$, where the input and output widths are $d_0 = d_L = 1$ and $d_j > 0$ for every $j < L$. Then the real function computed by its first $L$ layers is piecewise affine with at most $n$ pieces for some $n \le \left(2 \sum_{i=1}^{L} d_i / L\right)^L$. Widths after layer $L$ are unconstrained and may be zero; positivity of the traversed widths is needed.
