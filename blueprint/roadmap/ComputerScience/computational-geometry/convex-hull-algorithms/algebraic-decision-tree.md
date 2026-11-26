# Algebraic decision tree

Fix integers $N \ge 1$ and $d \ge 1$. A *$d$-th order algebraic decision tree* on inputs $z = (z_1, \dots, z_N) \in \mathbb{R}^N$ is a finite rooted tree in which each internal node is labelled by a polynomial $f \in \mathbb{R}[z_1, \dots, z_N]$ of degree at most $d$ and has three children, followed according to whether $f(z) < 0$, $f(z) = 0$ or $f(z) > 0$, and each leaf is labelled *yes* or *no*. The tree *decides* a set $W \subseteq \mathbb{R}^N$ if, for every input $z$, the path from the root following the signs reaches a leaf labelled *yes* exactly when $z \in W$. Its *height*, the largest number of internal nodes on a root-to-leaf path, is the worst-case number of tests. Orientation tests on points given by their coordinates are tests of degree $2$.

## Sources

- D. G. Kirkpatrick and R. Seidel, "The ultimate planar convex hull algorithm?", *SIAM Journal on Computing* 15(1) (1986), 287–299, <https://doi.org/10.1137/0215021>: Section 5, the definition of a $d$-th order algebraic decision tree (internal nodes labelled by polynomials of degree at most $d$, three outgoing edges for $<$, $=$ and $>$, leaves labelled YES or NO) and of deciding membership in a set $W$
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, "Lower Bound (Optional)": the $d$-th order algebraic decision tree, its three-way sign tests and the orientation test as a degree-two polynomial
