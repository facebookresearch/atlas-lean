# Jump consistent hash is uniform and monotone

For the idealized [jump consistent hash](jump-consistent-hash.md) and a fixed key $k$:

1. (balance) $ch(k, n)$ is uniformly distributed on $\{0, 1, \dots, n - 1\}$ for every $n \ge 1$;
2. (monotonicity) $ch(k, n+1) \in \{ch(k, n), n\}$, and $ch(k, n+1) = n$ with probability $1/(n + 1)$: when a bucket is added, only keys moving to the new bucket change bucket, and they make up the fraction $1/(n+1)$ of the keys;
3. $\Pr[ch(k, n) = ch(k, m)] = m/n$ for $1 \le m \le n$.

Statement 3 follows from 2, since the events of not jumping at $m, m+1, \dots, n-1$ are independent with probabilities $m/(m+1), \dots, (n-1)/n$, whose product is $m/n$; statement 1 follows by induction on $n$ from 2.

## Depends on

- [Jump consistent hash](jump-consistent-hash.md)

## Sources

- J. Lamping and E. Veach, "A fast, minimal memory, consistent hash algorithm", arXiv:1406.2294, 2014, <https://arxiv.org/abs/1406.2294>, section "Explanation of the algorithm": the requirement that $ch(k, n+1)$ stays at $ch(k, n)$ for $n/(n+1)$ of the keys and jumps to $n$ for the others, and the formula $P(ch(k, n) = ch(k, m)) = m/n$ for $n \ge m$.
