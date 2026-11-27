# Attention weights

For $n$ tokens with vectors $x_1, \dots, x_n \in \mathbb{R}^d$ (the rows of $X$), query and key matrices $W_Q, W_K \in \mathbb{R}^{d \times d_k}$ with $d_k \ge 1$, the scaled dot-product attention weights of query token $i$ are

$$\mathrm{softmax}_j\left(\frac{(x_i W_Q) \cdot (x_j W_K)}{\sqrt{d_k}}\right), \qquad j = 1, \dots, n.$$

There is no positional encoding and no mask.
