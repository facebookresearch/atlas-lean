# Space-efficient value stores from tiny pointers

Suppose a user stores, alongside each of up to $n$ keys, a tiny pointer (a *tiny retriever*) of expected size $O(1)$ bits. Then for any $r \in [\log^* n]$ there is a data structure storing a $v$-bit value for each key that, with high probability, answers queries in constant time, performs insertions and deletions in $O(r)$ time, and uses $n v + O(n \log^{(r)} n)$ bits of space, where $\log^{(r)}$ denotes the $r$-th iterated logarithm (Theorem 6). For constant $r$ all operations take constant time; if moreover $\log^{(r)} n = \omega(1)$ and $v \le \log n/\log^{(r)} n$, the space is $nv + O(n)$ bits.

## Proof sketch

Build a variable-size dereference table on $2n$ slots without allocating its store: $\mathrm{Allocate}(x)$ returns the tiny retriever $p$, and $s_x = \mathrm{Dereference}(x, p) \in [2n]$ is distinct for distinct stored keys. Store the pairs $(s_x, y)$ in a succinct hash table that uses $\log_2\binom{|U|}{n} + nv + O(n\log^{(r)} n)$ bits with constant-time queries and $O(r)$-time updates; since its keys come from the universe $[2n]$, $\log_2\binom{2n}{n} = O(n)$. The dereference table's own metadata takes $O(n)$ bits.

## Depends on

- [Tiny pointers and dereference tables](tiny-pointer.md)

## Proof depends on

- [Optimal sizes of tiny pointers](tiny-pointer-optimal-size.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Tiny Pointers", SODA (2023); ACM Transactions on Algorithms (2025), arXiv:2111.12800.
