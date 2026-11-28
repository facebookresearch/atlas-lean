# Tutte's matrix theorem and Lovász's randomized matching test

Let $G$ be a finite simple graph on $\{1, \dots, n\}$ with Tutte matrix $T_G$, and let $F$ be a field. $\det T_G \ne 0$ as a polynomial over $F$ if and only if $G$ has a perfect matching. Hence substituting independent uniform values from a finite subset $S \subseteq F$ for the indeterminates, and evaluating the determinant in $F$, gives a randomized test with one-sided error: it never reports a matching when none exists, and misses an existing perfect matching with probability at most $n/|S|$.

## Proof sketch

Permutations with an odd cycle cancel in pairs by reversing the cycle; the remaining permutations, all of whose cycles are even, contribute squares of matching monomials (the determinant is the square of the Pfaffian), which cannot cancel. The error bound is Schwartz-Zippel for a nonzero polynomial of degree at most $n$ over $F$. The field hypothesis is needed: over the ring $\mathbb{Z}/16\mathbb{Z}$, $G = K_2$ gives $\det T_G = x^2$, which vanishes at $4$ of the $16$ values, more than $n/|S| = 2/16$.

## Depends on

- [The Tutte matrix of a graph](tutte-matrix.md)

## Sources

- W. T. Tutte, "The Factorization of Linear Graphs", Journal of the London Mathematical Society 22, 1947.
- L. Lovász, "On Determinants, Matchings, and Random Algorithms", Fundamentals of Computation Theory (FCT 1979), Akademie-Verlag, 1979.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
- A. Gupta, CMU 15-850 Advanced Algorithms (Fall 2020) lecture notes, Ch. 8 "Graph Matchings III: Algebraic Algorithms": Theorem 8.3 (Schwartz-Zippel over a field $F$, values from $S \subseteq F$), Lemma 8.8 (one-sided test), Theorem 8.11 (Tutte matrix over any field). <http://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15850-f20/www/notes/lec8.pdf>
- CMU 15-859E Advanced Algorithms (Spring 2015), Lecture #11 "Matrix-based Algorithms for Matchings via Polynomial Identity Testing" (lecturer A. Gupta): Theorem 11.1 ($S \subseteq \mathbb{F}_q$), Theorem 11.3, Algorithm 2. <http://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15859-s15/www/lectures/lecture11.pdf>
