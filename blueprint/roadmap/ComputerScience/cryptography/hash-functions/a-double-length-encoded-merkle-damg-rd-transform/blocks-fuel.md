# Cutting at most k blocks off a bit string

For a block length $n$, a fuel $k \in \mathbb{N}$ and a bit string $P$, cutting at most $k$ blocks off $P$ is defined by recursion on $k$: with $k = 0$ the result is empty; with $k + 1$, if the first $n$ bits of $P$ exist (the prefix of length $\min(n, |P|)$ has length exactly $n$, i.e. $n \le |P|$), the result is that $n$-bit block followed by the blocks cut with fuel $k$ from $P$ with its first $n$ bits dropped, and otherwise it is empty.

For $n > 0$ this returns the first $\min(k, \lfloor |P|/n \rfloor)$ consecutive $n$-bit blocks of $P$. At $n = 0$ the test always succeeds and nothing is consumed, so the result is $k$ empty blocks.

Each step inspects only the first $n$ bits and never the length of the remaining list, so the cost is $O(1 + k(n+1))$ list operations; the bound $O(kn)$ fails at $n = 0$, where $k$ steps still run.
