# Embedding in the sphere

Let $G$ be a simple graph on a finite vertex set $V$, with darts (ordered pairs $(u, v)$ of adjacent vertices) and a permutation $\rho$ of the darts. The pair $(G, \rho)$ is spherical when $G$ is connected and $|V| - |E| + F = 2$, where $|E|$ is half the number of darts and $F$ is the number of faces, $\sum_d 1/|f(d)|$ over the darts $d$ with $|f(d)|$ the size of the face through $d$ under the face permutation $\varphi(u, v) = \rho(v, u)$.

This is a raw orbit-count test: it does not assume that $\rho$ is a [rotation system](is-rotation-system.md). Only when $\rho$ is a rotation system does it say that the rotation system describes an embedding of $G$ in the sphere. For an arbitrary permutation it can hold without any sphere embedding: for the $18$ darts of $K_{3,3}$, choose a permutation $\varphi$ with five cycles and set $\rho = \varphi \circ \mathrm{reverse}$; then $6 - 9 + 5 = 2$, yet $K_{3,3}$ is not planar.
