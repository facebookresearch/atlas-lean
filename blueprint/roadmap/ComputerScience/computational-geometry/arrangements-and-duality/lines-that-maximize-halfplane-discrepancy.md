# Lines that maximize halfplane discrepancy

Let $P$ be a finite nonempty set of points in the interior of $U = [0,1]^2$, and let $h$ be a halfplane of maximum discrepancy with respect to $P$, with bounding line $\ell$. Then either $\ell$ passes through exactly one point of $P$, which is the midpoint of $\ell \cap U$, or $\ell$ passes through at least two points of $P$. Otherwise $\ell$ could be translated, or rotated about its point of $P$, so that $\mu(h)$ moves away from $\mu_P(h)$ while $\mu_P(h)$ stays fixed. Such a line $\ell$ meets the interior of $U$: a line missing it gives discrepancy $0$, since $h \cap U$ is then $U$ or has area $0$ and contains no point of $P$, whereas $\Delta(P) > 0$. The interior assumption is needed: for $P = \{(0, 1/4)\}$ the halfplane $x \le 0$ has the maximum discrepancy $1$, but its point is not the midpoint of the side $x = 0$.

## Depends on

- [Halfplane discrepancy](halfplane-discrepancy.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 15, the Lemma on the halfplane of maximum discrepancy (types 1 and 2) and its proof
