# The interleaved ReLU matrix has full rank

Let $b_1 < x_1 < b_2 < x_2 < \dots < b_n < x_n$, that is, $b_i < x_i$ for every $i$ and $x_i < b_j$ whenever $i < j$. Then the matrix

$$
A = \big[\max(x_i - b_j, 0)\big]_{i, j = 1}^n
$$

is lower triangular, with diagonal entries $x_i - b_i > 0$, so $\det A \ne 0$.

The source also notes that the smallest eigenvalue of $A$ is $\min_i (x_i - b_i)$.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Appendix C, Lemma 1.
