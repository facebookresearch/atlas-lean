# Van Emde Boas operations use O(log log u) recursive calls

In the recursive van Emde Boas tree over a universe of size $u = 2^{2^d}$, the operations membership, insertion, deletion, minimum and strict successor are correct with respect to the represented finite set, and each performs at most $d + 1 = \log_2 \log_2 u + 1$ active recursive calls. In particular these ordered-set operations take $O(\log \log u)$ time, provided each call does $O(1)$ local work.

## Proof sketch

Keeping the minimum outside the clusters means that inserting into an empty cluster only sets its minimum, so when the summary must be updated the cluster call is constant time, and symmetrically for deletion of the last element. Successor first checks the cached maximum of the current cluster to decide whether to recurse into the cluster or into the summary. Each level therefore does one recursive call on a universe of size $\sqrt{u}$, and $d$ halvings of the exponent reach depth $0$.

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, 2015.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
