# Comparison-query cost model

In the *comparison-query model* over a linearly ordered key type, an algorithm is a decision tree whose internal nodes ask a query $x \le y$ on two keys and branch on the Boolean answer; all other computation is free, and the cost of a run is the number of queries asked. An algorithm written generically over the comparison oracle cannot inspect keys without asking, so its query count under any oracle is a well-defined cost; under the order's own oracle it computes its intended value.

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
