# Halfplane discrepancy

Let $P$ be a finite nonempty set of points in the unit square $U = [0,1]^2$. For a closed halfplane $h$ let $\mu(h)$ be the area of $h \cap U$ and $\mu_P(h) = |P \cap h| / |P|$. The *discrepancy* of $P$ with respect to $h$ is $\Delta_P(h) = |\mu(h) - \mu_P(h)|$, and the *halfplane discrepancy* of $P$ is $\Delta(P) = \sup_h \Delta_P(h)$, the supremum over all halfplanes. Points of $P$ on the boundary of $h$ are counted in $\mu_P(h)$. Since the complement of an open halfplane is a closed one with complementary measures, $\Delta(P)$ is also the supremum over open and closed halfplanes together, which is why an algorithm may count the boundary points all in or all out, whichever gives the larger discrepancy.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 15, "Halfplane Discrepancy": the definitions of $\mu(h)$, $\mu_P(h)$, $\Delta_P(h)$ and $\Delta(P)$, and the remark on points on the boundary line
