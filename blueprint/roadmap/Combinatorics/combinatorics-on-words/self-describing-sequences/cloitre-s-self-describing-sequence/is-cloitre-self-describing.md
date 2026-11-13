# Cloitre's self-describing property

A sequence $s : \mathbb{N} \to \mathbb{N}$ is
self-describing in Cloitre's sense when there is a sequence $b : \mathbb{N} \to \mathbb{N}$ with
$b(0) = 0$, $b$ strictly increasing, $s$ constant on each block $[b(n), b(n+1))$ and each value of
$s$ on a block different from each value on the next block (so the blocks are the maximal runs of
$s$), such that for every $n$, $2 s(n) = \sum_{b(n) \le j < b(n+1)} s(j)$.

In words, for every $n$ the $n$-th term $s(n)$ is half the sum of the $n$-th run; the condition is
stated with $2 s(n)$ to avoid truncated division in $\mathbb{N}$. For example, run sums
$2, 2, 4, 2, 2, 2, 2, 4, \ldots$ correspond to the terms $1, 1, 2, 1, 1, 1, 1, 2, \ldots$
