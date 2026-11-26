# A point outside the current disk lies on the new boundary

Let $p_1, \dots, p_n$ be points of $\mathbb{R}^2$, no four on a common circle, and let $B_i$ be the minimum enclosing disk of $p_1, \dots, p_i$. If $p_i \notin B_{i-1}$, then $p_i$ lies on the boundary circle of $B_i$.

## Proof depends on

- [Structure of the minimum enclosing disk](structure-of-the-minimum-enclosing-disk.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 21, the claim that if $p_i \notin B_{i-1}$ then $p_i$ is on the boundary of $B_i$
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Smallest enclosing circles and more", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides4b.pdf>: the incremental algorithm and its lemmas
