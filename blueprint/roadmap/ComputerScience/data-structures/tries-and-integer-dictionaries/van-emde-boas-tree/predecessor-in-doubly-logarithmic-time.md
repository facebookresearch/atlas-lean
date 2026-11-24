# Predecessor in doubly logarithmic time

Fix the universe $U = \{0, \dots, u - 1\}$ of $w$-bit integers, $u = 2^w$. A *recursive van Emde Boas tree* $V$ over $U$ stores a set $S \subseteq U$ as follows:
- the minimum $V.\min$, which is stored only here and not recursively, and the maximum $V.\max$;
- $\sqrt u$ clusters $V.\mathrm{cluster}[c]$, which are van Emde Boas trees over $\sqrt u$ elements. An element $x \ne V.\min$ with high half $c$ and low half $i$ of its bits is stored as $i$ in cluster $c$;
- a summary $V.\mathrm{summary}$, a van Emde Boas tree over $\sqrt u$ elements that holds the indices of the nonempty clusters.

**Theorem.**
1. A recursive van Emde Boas tree supports successor, predecessor, insertion and deletion in $O(\log\log u) = O(\log w)$ time in the word-RAM model, using $\Theta(u)$ space.
2. Replacing the arrays of clusters by hash tables and omitting empty clusters reduces the space to $\Theta(n)$ for $n = |S|$, with all operations in $O(\log\log u)$ time with high probability.
3. *Y-fast tries* achieve the same bounds, $O(\log\log u)$ time with high probability and $\Theta(n)$ space. They combine an *x-fast trie*, a hash table of all prefixes of the stored keys searched by binary search over prefix lengths, on $\Theta(n/w)$ representatives, with balanced search trees of size $\Theta(w)$ below.

**Proof.**
1. Each operation makes at most one recursive call on a structure over $\sqrt u$ elements, plus $O(1)$ work. A successor query recurses into its own cluster if its low half is below that cluster's maximum, and otherwise into the summary. An insertion into an empty cluster only sets that cluster's minimum, so recursing into the summary as well still costs $O(1)$ extra. So $T(u) \le T(\sqrt u) + O(1)$, which gives $T(u) = O(\log\log u)$.
2. Charge every hash-table entry to the minimum of its cluster. Each stored element is charged at most twice.
3. The binary search over the $w$ prefix lengths takes $O(\log w)$ hash lookups. Indirection charges the $O(w)$-time top-level updates to the $\Theta(w)$ updates in a bottom tree.

## Depends on

- [Two-level van Emde Boas tree](van-emde-boas.md)

## Background

- [Grouped y-fast trie](../y-fast-trie/grouped-yfast-trie.md)
- [The cell-probe model](../../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 11 "Integer data structures" (scribe notes, Spring 2012, revised Fall 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec11.pdf>:
    - Section 3: known bounds for the predecessor problem in the word-RAM, cell-probe and pointer-machine models;
    - Section 4: the recursive structure with clusters, a summary, a minimum that is not stored recursively, and a maximum; successor, insertion and deletion; and Theorem 1 ($O(\log\log u)$ time from $T(u) \le T(\sqrt u) + O(1)$);
    - Section 5.2: indirection;
    - Section 6: hashing for $\Theta(n)$ space, x-fast trees and y-fast trees.
