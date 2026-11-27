# Coreset for directional width

Let $P$ be a finite nonempty set of points in $\mathbb{R}^d$. For a unit vector $u$, the *directional width* of $P$ in direction $u$ is

$$W_P(u) = \max_{p \in P} (p \cdot u) - \min_{p \in P} (p \cdot u),$$

the distance between the two hyperplanes orthogonal to $u$ that sandwich $P$. For $0 < \varepsilon < 1$, a nonempty subset $C \subseteq P$ is an *$\varepsilon$-coreset for directional width* if $W_C(u) \ge (1 - \varepsilon) W_P(u)$ for every unit vector $u$.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 25, "Directional Width and Coresets": the directional width $W_P(u)$ and the definition of an $\varepsilon$-coreset for directional width
