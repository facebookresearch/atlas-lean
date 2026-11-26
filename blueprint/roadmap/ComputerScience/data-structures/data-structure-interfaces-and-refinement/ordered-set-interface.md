# Ordered-set interface

The *ordered-set interface* over a linearly ordered type $K$ has as state a finite set $S \subseteq K$, initially empty, and operations $\mathrm{contains}(x)$ (whether $x \in S$), $\mathrm{insert}(x)$, $\mathrm{delete}(x)$, $\mathrm{minimum}$ (the least element of $S$, or none) and $\mathrm{successor}(x)$ (the least element of $S$ strictly greater than $x$, or none). All operations are admissible, including duplicate insertions and deletions of absent keys; a bounded-universe implementation may restrict insertion to keys below a bound. Binary search trees, AVL trees, splay trees and van Emde Boas trees are implementations.

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
