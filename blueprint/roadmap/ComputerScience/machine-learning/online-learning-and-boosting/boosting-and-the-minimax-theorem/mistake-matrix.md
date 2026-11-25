# The mistake matrix

For $k$ hypotheses $h_1, \dots, h_k$ and a target $c$ on $n$ instances, the mistake matrix has a row for each instance and a column for each hypothesis:

$$M(x, j) = \begin{cases} 1 & h_j(x) \ne c(x), \\ 0 & h_j(x) = c(x). \end{cases}$$

For a distribution $Q$ on the instances, $\sum_x Q(x) M(x, j)$ is the weighted error of $h_j$ under $Q$. Freund and Schapire index the rows by hypotheses; the transpose used here lets the instances be the maximizing row player in the minimax theorem.

## Sources

- Y. Freund and R. E. Schapire, "Game theory, on-line prediction and boosting", *Proceedings of the Ninth Annual Conference on Computational Learning Theory* (COLT 1996), Section 3 (the mistake matrix) and Section 4.1.
