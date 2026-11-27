# Coresets for directional width compose

Let $X \subseteq Y \subseteq Z$ be finite nonempty subsets of $\mathbb{R}^d$ and $\varepsilon, \varepsilon' \in (0, 1)$ with $\varepsilon + \varepsilon' < 1$. If $X$ is an $\varepsilon$-coreset of $Y$ and $Y$ is an $\varepsilon'$-coreset of $Z$ for directional width, then $X$ is an $(\varepsilon + \varepsilon')$-coreset of $Z$, since $W_X(u) \ge (1 - \varepsilon)(1 - \varepsilon') W_Z(u) \ge (1 - \varepsilon - \varepsilon') W_Z(u)$ for every unit vector $u$.

The analogous union property fails: in $\mathbb{R}^1$ with $\varepsilon = 0.1$, $\{0.9, 9\}$ is an $\varepsilon$-coreset of $\{0, 0.9, 9\}$ and $\{1, 9.1\}$ is one of $\{1, 9.1, 10\}$, but their union has width $8.2 < 0.9 \cdot 10$.

## Depends on

- [Coreset for directional width](coreset-for-directional-width.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 25, the Chain Property (the Union Property stated next to it, without proof, is false as shown above)
