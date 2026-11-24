# Number of left-to-right maxima

For a permutation $\sigma$ of $\{0, 1, \dots, n-1\}$,
$\mathrm{lmax}(\sigma)$ is the number of positions $i$ such that $\sigma(j) < \sigma(i)$ for
every position $j < i$, that is, the number of entries larger than every entry to their left.

## Sources

- Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*, INTEGERS 26 (2026), Article A59, Section 1 (statistics).

## Related topics

- [Hiring problem](../../../../ComputerScience/randomized-algorithms/hiring-problem/README.md):
  the hire count of the hire-assistant scan is this statistic of the interview order, and its
  expectation over a random order is the harmonic number $H_n$.
