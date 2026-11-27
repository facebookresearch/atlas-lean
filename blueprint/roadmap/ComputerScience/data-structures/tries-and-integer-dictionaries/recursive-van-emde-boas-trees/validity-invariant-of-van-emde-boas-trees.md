# Validity invariant of recursive van Emde Boas trees

Call a recursive van Emde Boas tree *valid* if, at every node, the cached minimum and maximum are the least and greatest represented elements, the minimum does not occur in any cluster, an element other than the minimum occurs in exactly the cluster given by its high half, and the summary represents exactly the indices of the nonempty clusters. The empty tree is valid; insertion of an element not in the represented set and deletion of an element of the represented set map valid trees to valid trees whose represented sets are the set with the element added, respectively removed; and on valid trees, membership, minimum, strict successor and strict predecessor return the correct answers for the represented finite set.

## Proof sketch

By induction on the depth. Insertion into an empty node only sets the bounds; otherwise it swaps the new element with the minimum if smaller, inserts the other into its cluster, and updates the summary only when the cluster was empty, in which case the cluster insertion is the trivial one. Deletion is symmetric, recomputing the minimum from the summary's least cluster. The hypotheses on the element are needed: inserting the current minimum again skips the swap and stores a copy of the minimum in a cluster, and a following deletion then reloads that copy as the new minimum (Demaine, 6.046J Lecture 4, INSERT and DELETE).

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, 2015.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
