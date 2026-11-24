# Tensor product of $k$ vectors

For vectors $f_0, \dots, f_{k-1} \in \mathbb{R}^d$, their tensor product $f_0 \otimes \dots \otimes f_{k-1}$ is the vector of $\mathbb{R}^{[d]^k}$, with coordinates indexed by words $j = (j_0, \dots, j_{k-1})$, given by

$$
(f_0 \otimes \dots \otimes f_{k-1})_j = \prod_{i < k} (f_i)_{j_i} .
$$

For $k = 2$ this is Knuth's Hadamard product of two labelings.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §20, eq. (20.6).
