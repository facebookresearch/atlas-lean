# Inverted index and sorted postings intersection

For a finite corpus of documents numbered $1, \dots, N$, each a finite set of terms, the inverted index maps each term $t$ to its postings list: the
strictly increasing list of the documents that contain $t$. For strictly increasing lists $xs$ and $ys$ over a linear order, of lengths $x$ and $y$, the
two-pointer merge (compare the current heads; output and advance both on equality, otherwise advance the smaller) returns the strictly increasing list of
the elements common to both, and performs at most $x + y - 1$ comparisons when $x, y \ge 1$ and none otherwise. Here one comparison of the two
heads decides whether the first is smaller than, equal to or larger than the second; counting an equality test and an
order test separately, as two-branch implementations do, the bound becomes $2(x + y - 1)$.

## Proof

Invariant: every common element smaller than both current heads has been output, and no element is output that is not common. When the heads differ,
the smaller head cannot occur in the other list beyond its pointer, since that list is strictly increasing; on equality the element is common, and strict
increase prevents repeats. Each comparison advances at least one pointer, and the loop stops when one list is exhausted; the last comparison exhausts a list,
so at most $x + y - 1$ comparisons occur.

## Related topics

- [Index construction and postings compression](index-construction-and-postings-compression.md)

## Sources

- C. D. Manning, P. Raghavan and H. Schütze, *Introduction to Information Retrieval*, Cambridge University Press, 2008, Section 1.3, Figure 1.6 and the paragraph after it, pp. 10–11 (the merge algorithm for intersecting postings lists, in $O(x + y)$ operations); the exact count is the argument above.
