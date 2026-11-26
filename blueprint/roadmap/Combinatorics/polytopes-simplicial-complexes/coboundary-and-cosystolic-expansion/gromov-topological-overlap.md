# Gromov: coboundary expansion implies topological overlapping

For every $d \ge 1$ and $\varepsilon > 0$ there is $c = c(d, \varepsilon) > 0$ such that the following holds. If a pure $d$-dimensional complex $X$ is an $\varepsilon$-coboundary expander in every dimension $0 \le i < d$ (in the uniform normalized norms), then $X$ has the **$c$-topological overlapping property**: for every continuous map $\phi : X \to \mathbb{R}^d$ there is a point $p \in \mathbb{R}^d$ contained in $\phi(\sigma)$ for at least a $c$-fraction of the top faces $\sigma \in X(d)$.

## Proof sketch

Assume the overlapping fails. Then one constructs, dimension by dimension, cochains $f_i$ that record intersection parities of $\phi$-images of $i$-faces with a generic flag of affine subspaces; low overlap makes $\|\delta f_i\|$ small, so coboundary expansion produces $g_i$ with $f_i - \delta g_{i-1}$ small, and iterating to dimension $d$ yields a cochain that must be both zero and equal to the degree of a map of a sphere, a contradiction.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)

## Sources

- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
- T. Kaufman, D. Kazhdan, A. Lubotzky, "Ramanujan complexes and bounded degree topological expanders", FOCS (2014); Geometric and Functional Analysis 26 (2016), arXiv:1408.6351.
