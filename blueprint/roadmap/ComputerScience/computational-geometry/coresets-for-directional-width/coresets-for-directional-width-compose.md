# Coresets for directional width compose

Let $X, Y, Z, P, P'$ be finite subsets of $\mathbb{R}^d$ and $\varepsilon, \varepsilon' \in (0, 1)$ with $\varepsilon + \varepsilon' < 1$.
1. If $X$ is an $\varepsilon$-coreset of $Y$ and $Y$ is an $\varepsilon'$-coreset of $Z$ for directional width, then $X$ is an $(\varepsilon + \varepsilon')$-coreset of $Z$, since $(1 - \varepsilon)(1 - \varepsilon') \ge 1 - \varepsilon - \varepsilon'$.
2. If $X$ is an $\varepsilon$-coreset of $P$ and $X'$ is an $\varepsilon$-coreset of $P'$, then $X \cup X'$ is an $\varepsilon$-coreset of $P \cup P'$.

## Depends on

- [Coreset for directional width](coreset-for-directional-width.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 25, the Chain Property and the Union Property
