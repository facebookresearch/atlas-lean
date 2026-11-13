# Increasing-cycle permutation

A permutation $\tau$ of $\{0, \dots, n-1\}$ is an
increasing-cycle permutation when, for all $x$ and $y$ in $\{0, \dots, n-1\}$ such that
$\tau(x) \le x$ and $y$ lies in the same cycle of $\tau$ as $x$, we have $\tau(x) \le y$. That
is, whenever $\tau(x) \le x$, the value $\tau(x)$ is the least element of the cycle of $x$;
equivalently, each cycle of $\tau$ runs through its elements in increasing order and returns from
the largest to the least.

Set partitions of $\{0, \dots, n-1\}$ correspond bijectively to increasing-cycle permutations,
the blocks being the cycles (fixed points give singleton blocks), and partitions are counted
through this encoding.

## Sources

- Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*, Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the permutation `τ` whose cycles are the parts, with their elements in increasing order).
