# Gibbs variational principle, attainment

Let $X$ be a finite set, $E$ a real inner product space and $\phi : X \to E$ a sufficient statistic. If $X$ is nonempty then for every $\theta \in E$

$$
\sum_{x \in X} p_\theta(x)\bigl(\langle\phi(x), \theta\rangle - \log p_\theta(x)\bigr) = A(\theta),
$$

that is $A(\theta) = \langle\mathbb E_\theta[\phi(X)], \theta\rangle + H(p_\theta)$: the bound of the [upper-bound half](sum-mul-inner-sub-log-le.md) is attained at $q = p_\theta$, so $A(\theta) = \max_q\{\langle\mathbb E_q[\phi], \theta\rangle + H(q)\}$.

## Informally uses

- [The density is a probability distribution](density-pos-and-sum-eq-one.md): $\log p_\theta(x) = \langle\phi(x), \theta\rangle - A(\theta)$ and $\sum_x p_\theta(x) = 1$.

## Background

- [Gibbs variational principle](../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/is-greatest-integral-sub-kl-div.md): the general statement over measures, attained at the tilted measure; for $\nu$ uniform on $X$ the tilted measure is $p_\theta$, and this page is that special case.

## Sources

- M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational inference*, Found. Trends Mach. Learn. 1(1–2) (2008) 1–305, Theorem 3.4(c): the supremum in (3.45) is attained at the moment-matching mean parameter $\mu = \mathbb E_\theta[\phi(X)]$ (3.46).
