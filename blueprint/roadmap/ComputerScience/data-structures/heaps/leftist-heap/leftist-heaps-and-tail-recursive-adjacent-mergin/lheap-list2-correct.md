# Per-input correctness of list-to-heap construction

Over a linear order, for every list $L$, the leftist heap $h$ built from $L$ by tail-recursive
adjacent merging satisfies all of the following:

1. the multiset of elements of $h$ equals the multiset of elements of $L$;
2. $h$ has the min-heap property;
3. $h$ satisfies the leftist invariant.

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 15.4,
  Exercise 15.2.
