# Correctness and cost equivalence of tail-recursive heap construction

Over a linear order:

1. for every list $L$, the multiset of elements of the leftist heap built from $L$ by
   tail-recursive adjacent merging equals the multiset of elements of $L$;
2. for every list $L$, that heap has the min-heap property;
3. for every list $L$, that heap satisfies the leftist invariant (correct stored ranks, and left
   rank at least right rank at every node);
4. for every accumulator $C$ and every list $T$ of leftist heaps, the cost of tail-recursive
   adjacent merging of $T$ with accumulator $C$ equals the cost of non-tail-recursive adjacent
   merging of $T$.

Costs count merge steps only.

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 15.4,
  Exercise 15.2.
