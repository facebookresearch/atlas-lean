# A sequence along which fractions with new denominators become rare on average (representability formulation)

Some strictly increasing sequence $n_0 < n_1 < \cdots$ of positive integers has $\frac1N \sum_{k < N} \varphi_A(k)/n_k \to 0$ as $N \to \infty$, where for a sequence $n_0, n_1, \dots$ of positive integers and a natural number $k$, $\varphi_A(k)$ is the number of $m \in \{1, \dots, n_k\}$ such that $m/n_k$ cannot be written with denominator $n_j$ for any $j < k$: the reduced denominator $n_k/\gcd(m, n_k)$ divides no $n_j$ with $j < k$.

This is the original representability formulation of Erdős's paper (the definition preceding (20)): $m$ counts when $m/n_k$ cannot be written with any earlier denominator. Problem 1000 as printed in the database tests instead that the reduced denominator does not equal any earlier $n_j$, which counts more $m$: with an earlier denominator $6$ and $n_k = 10$, the fraction $5/10$ counts under that test ($2 \ne 6$) but not here ($1/2 = 3/6$). A zero average for the smaller count does not give one for the larger, so this statement does not settle the printed version.

This resolves [Erdős Problem 1000 in the original representability formulation (averages of new-denominator fraction counts)](new-fraction-average-tends-to-zero.md), the statement recorded as a proposition, in the affirmative; the resolution, recorded in Erdős Problems, Problem #1000, is due to J. A. Haight (PhD thesis).

## Sources

- T. F. Bloom, Erdős Problems, Problem #1000, https://www.erdosproblems.com/1000.
- P. Erdős, Problems and results on diophantine approximations, Compositio Math. 16 (1964), 52–65, definition preceding (20), https://combinatorica.hu/~p_erdos/1964-24.pdf.
