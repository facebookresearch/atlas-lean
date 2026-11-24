# Environment-packing term

For a map $\mathit{acc}$ from natural numbers to target terms
and a natural number $n$, the environment-packing term of $\mathit{acc}$ and $n$ is the target
term $(\mathit{acc}(0), (\mathit{acc}(1), \dots (\mathit{acc}(n - 1), \mathsf{unit})\dots))$
packing $\mathit{acc}(0), \dots, \mathit{acc}(n - 1)$ as nested pairs ending in $\mathsf{unit}$.
Recursively, it is $\mathsf{unit}$ for $n = 0$, and for $n + 1$ it is the pair of
$\mathit{acc}(0)$ and the environment-packing term of $i \mapsto \mathit{acc}(i + 1)$ and $n$.
