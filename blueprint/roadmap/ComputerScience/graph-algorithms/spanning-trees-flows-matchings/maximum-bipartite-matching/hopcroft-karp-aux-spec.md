# Correctness of the phase loop

Let $\mu$ be a valid partner array (a matching of the
graph) on $b$ right vertices, and let $n \in \mathbb{N}$ be a fuel with
$b < |\mathrm{matched}(\mu)| + n$, where $\mathrm{matched}(\mu)$ is the set of right vertices with
a partner in $\mu$; so $n$ exceeds the number of unmatched right vertices. Let $\mu'$ be the
result of the Hopcroft–Karp phase loop with fuel $n$ from $\mu$. Then $\mu'$ is valid, and every
matching $M$ of the graph satisfies $|M| \le |\mathrm{pairs}(\mu')|$, where $\mathrm{pairs}(\mu')$
is the set of pairs $(i, j)$ with $\mu'(j) = i$.
