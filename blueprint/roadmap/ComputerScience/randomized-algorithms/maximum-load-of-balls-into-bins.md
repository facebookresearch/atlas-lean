# Maximum load of balls into bins

Throw $n$ balls independently and uniformly at random into $n$ bins. For every $c > 0$ there is a constant $C$ such that, for all sufficiently large $n$, the probability that some bin receives at least $C \ln n / \ln \ln n$ balls is at most $n^{-c}$. The proof bounds the probability that a fixed bin receives at least $k$ balls by $\binom{n}{k} n^{-k} \le (e/k)^k$ and takes a union bound over the $n$ bins.

## Sources

- A. Gupta, *Advanced Algorithms*, lecture notes for CMU 15-850, Fall 2020, <https://www.cs.cmu.edu/~15850/notes/cmu850-f20.pdf>
