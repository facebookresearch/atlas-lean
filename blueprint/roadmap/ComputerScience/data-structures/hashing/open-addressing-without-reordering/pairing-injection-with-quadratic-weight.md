# An injection of index pairs with cost $O(i j^2)$

There is an injection $\phi : \mathbb{Z}_{\ge 1} \times \mathbb{Z}_{\ge 1} \to \mathbb{Z}_{\ge 1}$ with $\phi(i, j) = O(i j^2)$ for all $i, j \ge 1$. Hence any two-dimensional family of probe positions $h_{i,j}(x)$ can be serialized into a single probe sequence in which the position $h_{i,j}(x)$ appears at index $O(i j^2)$.

## Proof sketch

Enumerate pairs in nondecreasing order of the weight $i j^2$, breaking ties arbitrarily, and let $\phi(i, j)$ be the rank. The number of pairs of weight at most $t$ is $\sum_{j \ge 1} \lfloor t / j^2 \rfloor \le t \sum_{j \ge 1} j^{-2} = \frac{\pi^2}{6} t < 2t$, so a pair of weight $t = i j^2$ has rank below $2 i j^2$. This gives the bound with constant $2$. (Farach-Colton, Krapivin and Kuszmaul prove $\phi(i, j) = O(i j^2)$ with an explicit binary encoding, writing the bits of $j$ each preceded by a $1$, then a $0$, then the bits of $i$.)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305, Lemma 1.
