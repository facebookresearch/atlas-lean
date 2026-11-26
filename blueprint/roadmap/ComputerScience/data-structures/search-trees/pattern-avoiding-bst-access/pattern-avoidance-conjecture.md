# Pattern-avoidance conjecture for binary search trees

The *pattern-avoidance conjecture* (Chalermsook, Goswami, Kozma, Mehlhorn and Saranurak, FOCS 2015) asserts that for every fixed permutation $\pi$ there is a constant $c_\pi$ such that every $\pi$-avoiding permutation access sequence $X \in S_n$ satisfies $\mathrm{OPT}(X) \le c_\pi\, n$, i.e. pattern-avoiding inputs have $O(1)$ optimal amortized cost per access.

## Depends on

- [Pattern-avoiding access sequences](pattern-avoiding-access-sequence.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
