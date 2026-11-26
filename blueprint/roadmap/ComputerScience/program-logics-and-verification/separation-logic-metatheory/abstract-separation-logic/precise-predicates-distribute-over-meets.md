# Precise predicates distribute separating conjunction over intersections

Let $(\Sigma, \bullet, u)$ be a [separation algebra](separation-algebras.md).

1. Every singleton predicate $\{\sigma\}$ is [precise](precise-predicates.md).
2. A predicate $p$ is precise if and only if $\left(\bigcap X\right) \ast p = \bigcap \{x \ast p : x \in X\}$ for every nonempty family $X$ of predicates.

The empty family is excluded because $\bigcap \emptyset = \Sigma$ and $\Sigma \ast p$ is in general a proper subset of $\Sigma$. Conversely, injectivity of $\sigma \bullet (\cdot)$, the cancellativity in the definition of a separation algebra, is equivalent to the distribution law for singletons $p = \{\sigma\}$.

## Depends on

- [Precise predicates](precise-predicates.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007; extended version of April 13, 2007, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-long.pdf>, Section 2, Lemma 4 and the remark after it, stated there for all families $X$.
