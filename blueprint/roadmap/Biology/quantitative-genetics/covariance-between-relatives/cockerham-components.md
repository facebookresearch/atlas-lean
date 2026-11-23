# Cockerham–Kempthorne variance components

Cockerham–Kempthorne components consist of a natural number $n$ (the highest order kept) and real numbers $V_{ij}$ for $i, j \in \mathbb{N}$ (the component with $i$ additive and $j$ dominance factors: $V_{10} = V_A$, $V_{01} = V_D$, $V_{20} = V_{AA}$, ...) such that

- $V_{ij} \ge 0$ for all $i, j$;
- $V_{00} = 0$;
- $V_{ij} = 0$ whenever $i > n$ or $j > n$.

The representation of the genetic covariance of relatives by these components ([Cockerham form](cov.md)) is a hypothesis for many loci; for one locus it is proved ([one locus in Cockerham form](rel-cov-eq-cov.md)).
