# Two-vector bilinear fingerprints over finite fields

Let $F$ be a finite field, $M$ a nonzero $m \times n$ matrix over $F$, and $r \in F^m$, $s \in F^n$ independent and uniform. Then

$$
\Pr[r^{\mathsf T} M s \ne 0] = \Pr[Ms \ne 0]\Bigl(1 - \frac{1}{|F|}\Bigr) \ge \Bigl(1 - \frac{1}{|F|}\Bigr)^2,
$$

with equality when $M$ is a nonzero outer product (including characteristic $2$). In particular, two matrices $A \ne B$ are distinguished by the test $r^{\mathsf T}As = r^{\mathsf T}Bs$ with probability at least $(1 - 1/|F|)^2$.

## Proof sketch

Since $M \ne 0$, $s \mapsto Ms$ is a nonzero linear map, so $Ms \ne 0$ with probability at least $1 - 1/|F|$ (its kernel is a proper subspace). Given $Ms = v \ne 0$, $r \mapsto r^{\mathsf T}v$ is a nonzero functional, nonzero with probability exactly $1 - 1/|F|$. For a rank-one $M = uw^{\mathsf T}$ the first event has probability exactly $1 - 1/|F|$.

## Depends on

- [Uniform distribution on a finite type](../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 9–10, March 2007.
