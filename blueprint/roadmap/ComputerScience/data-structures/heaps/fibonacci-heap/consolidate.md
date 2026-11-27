# Consolidation of a forest

The consolidation of a list of Fibonacci trees is defined
recursively: the consolidation of the empty list is the empty list, and the consolidation of a
list with first tree $t$ and remaining list $L$ is the insertion of $t$ into the consolidation
of $L$.

Each insertion links trees of equal stored degree as in binary addition, so the result has
strictly increasing, hence distinct, stored root degrees, as in the consolidate step of CLRS.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 19.2 (procedure CONSOLIDATE).
