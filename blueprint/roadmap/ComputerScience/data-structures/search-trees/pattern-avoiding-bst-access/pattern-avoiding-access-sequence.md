# Pattern-avoiding access sequences

For a permutation $\pi \in S_k$, a sequence $X = (x_1, \dots, x_m)$ of distinct keys *contains* $\pi$ if there are indices $i_1 < \dots < i_k$ such that $x_{i_a} < x_{i_b}$ if and only if $\pi(a) < \pi(b)$, for all $a, b$; otherwise $X$ *avoids* $\pi$. A permutation access sequence $X \in S_n$ is $\pi$-avoiding if it avoids $\pi$ as a sequence. Sequential access $1, 2, \dots, n$ avoids $21$.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
