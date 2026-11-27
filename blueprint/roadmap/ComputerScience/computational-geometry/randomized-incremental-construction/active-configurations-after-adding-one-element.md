# Active configurations after adding one element

Let $S = (X, \Pi, D, K)$ be a configuration space, $R \subseteq X$ and $y \in X \setminus R$. The configurations in $T(R)$ that are not in conflict with $y$ are exactly the configurations in $T(R \cup \{y\})$ that do not have $y$ in their defining set. Hence

$$|T(R)| - |\{\Delta \in T(R) : y \in K(\Delta)\}| = |T(R \cup \{y\})| - \deg(y, R \cup \{y\}).$$

## Depends on

- [Configuration space](configuration-space.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 8 (The configuration space framework), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%208.pdf>: Lemma 8.6 and its proof
