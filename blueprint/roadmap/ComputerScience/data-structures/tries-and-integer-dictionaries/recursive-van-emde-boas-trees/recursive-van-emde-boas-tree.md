# Recursive van Emde Boas tree with excluded minimum

For $d \ge 0$ let $u_d = 2^{2^d}$. A *van Emde Boas tree* of depth $0$ stores a subset of $\{0, 1\}$ by its minimum and maximum. A tree of depth $d + 1$ over $[u_{d+1}]$ stores its minimum and maximum (or an empty marker); the minimum is *not* stored recursively. Every other element $x$ is written as $x = h \sqrt{u_{d+1}} + \ell$ with $h, \ell \in [u_d]$ and stored as $\ell$ in the depth-$d$ *cluster* number $h$, and a depth-$d$ *summary* tree stores the set of indices of nonempty clusters. Membership, insertion, deletion and successor each make at most one non-trivial recursive call, into either one cluster or the summary.

## Depends on

- [Two-level van Emde Boas tree](../van-emde-boas-tree/van-emde-boas.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, 2015.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- P. van Emde Boas, R. Kaas and E. Zijlstra, "Design and Implementation of an Efficient Priority Queue", Mathematical Systems Theory 10, 1977.
