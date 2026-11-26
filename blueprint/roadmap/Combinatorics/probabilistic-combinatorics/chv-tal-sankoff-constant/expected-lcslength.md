# Expected length of a longest common subsequence

For $n \in \mathbb{N}$, the expected LCS
length $E_n$ is the average of $\mathrm{LCS}(x, y)$, the length of a longest common subsequence of
$x$ and $y$, over all ordered pairs $(x, y)$ of binary strings of length $n$: it is the sum of
$\mathrm{LCS}(x, y)$ over these pairs divided by their number $4^n$. Equivalently, $E_n$ is the
expectation of $\mathrm{LCS}(x, y)$ for two independent uniformly random binary strings $x$, $y$
of length $n$.
