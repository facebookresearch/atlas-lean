# Real world of the PRF experiment

Let $K$, $X$, $Y$ and $S$ be finite sets with $K$, $Y$
and $S$ nonempty, let $F : K \to X \to Y$ be a keyed function and let $D$ be a distinguisher: an
oracle algorithm with coins in $S$ that queries a function $X \to Y$ and outputs a bit. The real
world is the distribution of the output of $D$ with coins $s$ and oracle $F(k, \cdot)$, where the
pair $(k, s)$ is uniform on $K \times S$.
