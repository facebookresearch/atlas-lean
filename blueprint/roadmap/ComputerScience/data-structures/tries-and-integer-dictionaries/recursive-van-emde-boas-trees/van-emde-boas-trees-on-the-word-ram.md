# Van Emde Boas trees on the Word RAM

There is one word-RAM program that, for every depth $d$, initializes an empty van Emde Boas tree over $[u]$ with $u = 2^{2^d}$ using $O(u)$ words, and performs membership, insertion of an element not in the represented set, and strict successor on it, each in $O(1 + \log \log u)$ worst-case time. Hence a dynamic ordered set over a universe of size $u$ supports these operations in $O(\log \log u)$ worst-case time with $O(u)$ space (Schwarz, Stanford CS166 Lecture 14: lookups, insertions and successor queries in $O(\log \log U)$ time, slides 99, 104, 109 and 110, with the minimum kept outside the clusters so that inserting into an empty tree is worst-case $O(1)$, slide 98, and $\Theta(U)$ space for the complete tree, slides 111-112; Demaine, 6.046J Lecture 4: $T(u) = T(\sqrt{u}) + O(1)$ for Insert and Successor).

## Proof sketch

The initializer computes the universe sizes and spans by the layout recurrence, tabulates split sizes and child spans per depth, and writes all headers by a depth-first traversal with per-depth counters, in $O(u)$ instructions. Each operation descends at most $d + 1$ records, using the tabulated offsets to locate the summary and the required cluster in $O(1)$ instructions per level, so a fixed register count and no depth-dependent code suffice.

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Van Emde Boas operations use O(log log u) recursive calls](van-emde-boas-recursion-depth.md)
- [Contiguous layout of a fully allocated van Emde Boas tree](contiguous-van-emde-boas-layout.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, 2015.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- K. Schwarz, "van Emde Boas Trees" (Lecture 14), CS166 Data Structures, Stanford University, Spring 2016, slides (PDF pages) 7, 76, 98-112: <http://web.stanford.edu/class/archive/cs/cs166/cs166.1166/lectures/14/Slides14.pdf>.
- P. van Emde Boas, R. Kaas and E. Zijlstra, "Design and Implementation of an Efficient Priority Queue", Mathematical Systems Theory 10, 1977.
