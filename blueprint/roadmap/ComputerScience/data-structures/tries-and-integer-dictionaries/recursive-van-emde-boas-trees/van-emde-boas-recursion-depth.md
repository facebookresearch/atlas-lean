# Van Emde Boas operations use O(log log u) recursive calls

In the recursive van Emde Boas tree over a universe of size $u = 2^{2^d}$, the operations insertion of an element not in the represented set, deletion of an element of the represented set, minimum and strict successor are correct with respect to the represented finite set, and each makes at most one non-trivial recursive call per level, so its running time satisfies $T(u) \le T(\sqrt{u}) + O(1)$ and it makes $O(\log \log u)$ recursive calls. In particular these ordered-set operations take $O(\log \log u)$ time, provided each call does $O(1)$ local work (Demaine, 6.851 Lecture 11, Section 11.3 for the operations, Section 11.4 for the structure and the operations on it, and Theorem 33: "we only recurse once" and $T(u) = O(\log \log u)$ for successor, insertion and deletion; Demaine, 6.046J Lecture 4: $T(u) = T(\sqrt{u}) + O(1)$ for SUCCESSOR, INSERT and DELETE, "If the first call is executed, the second call only takes O(1) time").

## Proof sketch

Keeping the minimum outside the clusters means that inserting into an empty cluster only sets its minimum, so when the summary must be updated the cluster call is constant time, and symmetrically for deletion of the last element. Successor first checks the cached maximum of the current cluster to decide whether to recurse into the cluster or into the summary. Each level therefore does one recursive call on a universe of size $\sqrt{u}$, and $d$ halvings of the exponent reach depth $0$. Counting the top-level call, each operation makes at most $d + 1 = \log_2 \log_2 u + 1$ non-trivial calls, one per depth.

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, Spring 2015, lecture notes, "Maintain Min and Max", "Don't store Min recursively", SUCCESSOR, INSERT lines 1-10 and DELETE lines 1-15: <https://ocw.mit.edu/courses/6-046j-design-and-analysis-of-algorithms-spring-2015/resources/lecture-4-notes/>.
- E. D. Demaine, Lecture 11 (March 22, 2012; scribes S. Fingeret, S. Rao and P. Christiano), 6.851 Advanced Data Structures, MIT, Spring 2012, scribe notes, Sections 11.3 and 11.4 and Theorem 33: <https://courses.csail.mit.edu/6.851/spring12/scribe/2012scribes.pdf>.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
