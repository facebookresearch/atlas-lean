# Reservoir sampling

Let $1 \le k$ and let a stream $a_1, a_2, \dots$ arrive one item at a time, with its length $m \ge k$ unknown in advance. *Reservoir sampling* keeps a reservoir $R$ of $k$ stream positions, together with their items:
- the first $k$ positions fill $R$;
- for $i > k$, with probability $k/i$, position $i$ replaces a position chosen uniformly at random from $R$, and otherwise $R$ is unchanged.

All random choices are independent.

**Theorem.** After $m$ items, $R$ is a uniformly random $k$-element subset of the positions $\{1, \dots, m\}$. The sample is of *positions*: if the stream repeats an item, the sampled items may repeat. In particular, for $k = 1$, the kept position is uniform on $\{1, \dots, m\}$. This is the case used to choose a random stream position in one pass.

**Proof.** By induction on $m \ge k$. For $m = k$, the reservoir holds all positions. Suppose $R$ is uniform over the $k$-subsets of $\{1, \dots, m\}$ and item $m + 1$ arrives. A $k$-subset $T$ not containing $m + 1$ is the new reservoir exactly when $R = T$ and no replacement happens. This has probability $\binom{m}{k}^{-1}(1 - \tfrac{k}{m+1}) = \binom{m+1}{k}^{-1}$. A subset $T = T' \cup \{m + 1\}$ with $|T'| = k - 1$ arises when a replacement happens and $R$ is one of the $m - k + 1$ sets $T' \cup \{p\}$ with $p \notin T'$ whose element $p$ is evicted. This has probability $\tfrac{k}{m+1} \cdot (m - k + 1)\binom{m}{k}^{-1} \cdot \tfrac{1}{k} = \binom{m+1}{k}^{-1}$.

## Background

- [The Morris approximate counter](the-morris-approximate-counter.md)

## Sources

- A. Chakrabarti, *Data Stream Algorithms*, lecture notes, Dartmouth College (update of 1 July 2025), <https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf>, Section 6.2, Algorithm 10: choosing a uniformly random stream position in one pass by replacing the kept position with the $m$-th one with probability $1/m$, called reservoir sampling there. The case of $k > 1$ is proved here.
