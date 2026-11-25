# Expected chain length under universal hashing

A family $H$ of functions $U \to \{0, \dots, m - 1\}$ is [universal](../universal-hashing/is-universal.md) if $\Pr_{h \in H}[h(x) = h(y)] \le 1/m$ for all $x \ne y$, with $h$ drawn uniformly from $H$. It is *near-universal* if the bound is $2/m$. In a hash table with *chaining*, slot $i$ holds a list of the stored keys $x$ with $h(x) = i$. Searching for $x$ takes time $O(1 + \ell(x))$, where $\ell(x)$ is the length of the list in slot $h(x)$. Let $n$ keys be stored and let $\alpha = n/m$ be the *load factor*.

**Theorem.** Let $h$ be drawn uniformly from a universal family.
1. For a key $x$ that is not stored, $\mathbb{E}[\ell(x)] \le \alpha$.
2. For a stored key $x$, $\mathbb{E}[\ell(x)] \le 1 + (n - 1)/m < 1 + \alpha$.
3. Hence every search, insertion and deletion takes expected time $O(1 + \alpha)$. Under near-universal hashing the bounds become $2\alpha$ and $1 + 2\alpha$.

The expected *worst-case* chain length is larger. With ideal random hashing and $n = m$, the longest chain has length $\Theta(\log n / \log\log n)$ with high probability.

**Proof.** Write $\ell(x) = \sum_{y} [h(y) = h(x)]$, summing over the stored keys $y$. By linearity of expectation, each $y \ne x$ contributes at most $1/m$, and $y = x$, if stored, contributes $1$.

## Depends on

- [Universal hash family](../universal-hashing/is-universal.md)
- [Hash table with separate chaining](../hash-table-with-separate-chaining/hash-table.md)

## Sources

- J. Erickson, *Algorithms*, lecture notes, Lecture 5 "Hash Tables" (Spring 2017), University of Illinois, <https://jeffe.cs.illinois.edu/teaching/algorithms/notes/05-hashing.pdf>: Section 5.3 (universal and near-universal families), Section 5.4 (chaining, $\ell(x) = \sum_y C_{x,y}$, $\mathbb{E}[\ell(x)] = n/m$ for a key not in the table under universal hashing, $2\alpha$ under near-universal hashing, expected search time $\Theta(1 + \alpha)$, and the caveat on worst-case search time), and Section 5.6, Lemma 5 (the fullest of $n$ bins holds $O(\log n/\log\log n)$ balls with high probability).
