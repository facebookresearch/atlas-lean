# Gluing lemma

Let $\pi_{12}$ be a probability measure on $X_1 \times X_2$ and $\pi_{23}$ a probability measure on
$X_2 \times X_3$ such that the second marginal of $\pi_{12}$ equals the first marginal of $\pi_{23}$.
If $X_3$ is a standard Borel space, there is a probability measure $\pi$ on
$(X_1 \times X_2) \times X_3$ whose marginal on $X_1 \times X_2$ is $\pi_{12}$ and whose marginal on
$X_2 \times X_3$ is $\pi_{23}$.

The proof disintegrates $\pi_{23}$ with respect to its first coordinate,
$\pi_{23}(dx_2\,dx_3) = \pi_{23}(dx_3 \mid x_2)\, \mu_2(dx_2)$, and sets
$\pi(dx_1\,dx_2\,dx_3) = \pi_{12}(dx_1\,dx_2)\, \pi_{23}(dx_3 \mid x_2)$, as in Villani's informal
argument. Villani assumes all three spaces Polish; only $X_3$ needs to be standard Borel here.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Chapter 1, Gluing lemma.
