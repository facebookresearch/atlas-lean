# Length of a closed tour

For points $x_0, \dots, x_{n-1}$ in the Euclidean plane and a
permutation $\sigma$ of $\{0, \dots, n-1\}$, the tour length is
$\sum_{i=0}^{n-1} \lVert x_{\sigma(i)} - x_{\sigma(i+1 \bmod n)} \rVert$, the length of the closed
tour that visits $x_{\sigma(0)}, \dots, x_{\sigma(n-1)}$ in this order and returns to its start.
