# Wasserstein distance controlled by total variation

Let $X$ be a second-countable pseudo-extended metric space whose $\sigma$-algebra contains the open
sets, and $D \ge 0$ a real number with $d(x, y) \le D$ for all $x, y \in X$. For all probability measures $\mu$ and $\nu$ on $X$,
$W_1(\mu, \nu) \le D \cdot \sup_B |\mu(B) - \nu(B)|$, where the supremum over measurable sets $B$ is
the total variation distance of $\mu$ and $\nu$.

## Idea

On a space of finite diameter at most $D$, mass that has to move travels at most $D$, and only the excess of
one measure over the other has to move. A coupling that leaves the common part of $\mu$ and $\nu$ in
place and moves the excess $(\mu - \nu)_+$ onto the deficit $(\mu - \nu)_-$, both of mass at most the
total variation distance, costs at most $D$ times that distance. So on such a space convergence in
total variation implies convergence in $W_1$. The converse fails: on $[0, 1]$ with its Borel sets,
$W_1(\delta_{1/n}, \delta_0) = 1/n \to 0$, while the total variation distance of $\delta_{1/n}$ and
$\delta_0$ is $1$, attained at $B = \{0\}$.

## Statements

- [Wasserstein distance controlled by total variation](wasserstein-one-le-mul-total-variation-d.md)

## Background

- [Wasserstein distance](../wasserstein-distance/README.md): the distance $W_1$.
- [Kantorovich duality](../../kantorovich-duality/README.md): couplings, used in the proof.
