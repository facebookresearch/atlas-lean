# Validity invariant of recursive van Emde Boas trees

Call a recursive van Emde Boas tree *valid* if, at every node, the cached minimum and maximum are the least and greatest represented elements, the minimum does not occur in any cluster, an element other than the minimum occurs in exactly the cluster given by its high half, and the summary represents exactly the indices of the nonempty clusters. The empty tree is valid; insertion of an element not in the represented set and deletion of an element of the represented set map valid trees to valid trees whose represented sets are the set with the element added, respectively removed; and on valid trees, minimum, strict successor and strict predecessor return the correct answers for the represented finite set. This is the correctness of the van Emde Boas tree whose minimum is not stored recursively and whose maximum is, as a structure for a dynamic set $S$ that inserts into $S$, deletes from $S$ and reports the successor and predecessor of a query in $S$ (Demaine, 6.851 Lecture 11, Section 11.3 for the operations and Section 11.4 for the structure and the operations on it; Demaine, 6.046J Lecture 4, "Don't store Min recursively", INSERT and DELETE), stated through an invariant.

## Proof sketch

By induction on the depth. Insertion into an empty node only sets the bounds; otherwise it swaps the new element with the minimum if smaller, inserts the other into its cluster, and updates the summary only when the cluster was empty, in which case the cluster insertion is the trivial one. Deletion is symmetric, recomputing the minimum from the summary's least cluster. The hypotheses on the element are needed: inserting the current minimum again skips the swap and stores a copy of the minimum in a cluster, and a following deletion then reloads that copy as the new minimum (Demaine, 6.046J Lecture 4, INSERT and DELETE).

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, Spring 2015, lecture notes, "Maintain Min and Max", "Don't store Min recursively", SUCCESSOR, INSERT lines 1-10 and DELETE lines 1-15: <https://ocw.mit.edu/courses/6-046j-design-and-analysis-of-algorithms-spring-2015/resources/lecture-4-notes/>.
- E. D. Demaine, Lecture 11 (March 22, 2012; scribes S. Fingeret, S. Rao and P. Christiano), 6.851 Advanced Data Structures, MIT, Spring 2012, scribe notes, Sections 11.3 and 11.4 and Theorem 33: <https://courses.csail.mit.edu/6.851/spring12/scribe/2012scribes.pdf>.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
