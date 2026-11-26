# Fenwick-tree operations take logarithmic time

In 0-indexed form, a [Fenwick tree](fenwick-tree.md) over an array $A[0..N-1]$ of elements of a commutative monoid stores $T_i = \sum_{j = g(i)}^{i} A_j$, where $g(i) = i \mathbin{\&} (i + 1)$ clears the trailing $1$ bits of $i$. The [one-indexed convention](fenwick-tree.md) uses $i - \mathrm{lowbit}(i) + 1$ instead, and is equivalent.

**Theorem.**
1. The [prefix sum](prefix-sum.md) $A_0 + \cdots + A_r$ equals $T_r + T_{g(r)-1} + T_{g(g(r)-1)-1} + \cdots$, stopping when the index becomes negative. This sum has at most $\lfloor \log_2 N \rfloor + 1$ terms.
2. A [point update](add.md) at position $i$ must change exactly the $T_j$ with $g(j) \le i \le j$. These are $j = i, h(i), h(h(i)), \dots < N$, where $h(j) = j \mathbin{|} (j + 1)$ sets the lowest $0$ bit, so there are at most $\lceil \log_2 N \rceil + 1$ of them.

So both operations take $O(\log N)$ time.

**Proof.** The ranges $[g(r), r], [g(g(r) - 1), g(r) - 1], \dots$ tile $[0, r]$. Each step $r \mapsto g(r) - 1$ turns the lowest $1$ bit of $r + 1$ into $0$, so the number of $1$ bits of $r + 1$ decreases by $1$. For updates, let $j$ have exactly $t$ trailing $1$ bits. Then $[g(j), j]$ is the set of numbers that agree with $j$ on all bits from position $t$ up. So $g(j) \le i \le j$ holds exactly when bit $t$ of $i$ is $0$ and $j = i \mathbin{|} (2^t - 1)$. Ordered by $t$, these $j$ are $i, h(i), h(h(i)), \dots$, because $h$ sets the lowest $0$ bit and the bits between consecutive $0$ bits of $i$ are already $1$. Since $j < N$ forces $2^t \le N$, there are at most $\lfloor \log_2 N \rfloor + 1$ of them.

## Depends on

- [Fenwick tree](fenwick-tree.md)
- [Fenwick tree prefix sum](prefix-sum.md)
- [Point update of a Fenwick tree](add.md)

## Sources

- cp-algorithms, "Fenwick Tree", <https://cp-algorithms.com/data_structures/fenwick.html>: the definition $T_i = \sum_{j=g(i)}^{i} A_j$ with $g(i) = i \mathbin{\&} (i + 1)$, prefix-sum queries and updates in $O(\log N)$ time, and the enumeration of the indices $j$ with $g(j) \le i \le j$ by repeatedly setting the lowest unset bit. The bit-counting bound is written out here.
