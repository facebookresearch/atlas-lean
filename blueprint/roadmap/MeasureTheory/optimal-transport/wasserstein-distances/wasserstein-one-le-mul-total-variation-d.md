# Wasserstein distance controlled by total variation

Let $X$ be a second-countable pseudo-extended metric space whose σ-algebra contains the open sets,
and assume $d(x, y) \le D$ for all $x, y \in X$. For all probability measures $\mu, \nu$ on $X$,

$$W_1(\mu, \nu) \le D \cdot \sup_B |\mu(B) - \nu(B)|,$$

the supremum over measurable sets $B$ being the
[total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
of this graph.

Proof (the transference plan of Villani's proof of Theorem 6.15): take a Hahn set $S$ for $\mu - \nu$,
split $\mu = \alpha + m$ and $\nu = \beta + m$ with common part $m = \nu|_S + \mu|_{S^c}$, excess
$\alpha = (\mu - \nu)_+$ and deficit $\beta = (\mu - \nu)_-$, both of mass
$a = \mu(S) - \nu(S) \le \sup_B |\mu(B) - \nu(B)|$, and use the coupling
$\pi = (\mathrm{id}, \mathrm{id})_\# m + a^{-1}\, \alpha \otimes \beta$, whose cost is at most $D a$.

Villani's $\|\mu - \nu\|_{TV}$ is the total variation norm (his Conventions), so
$\|\mu - \nu\|_{TV} = 2 \sup_B |\mu(B) - \nu(B)|$; equation (6.11) reads
$\|\mu - \nu\|_{TV} = 2 \inf P[X \ne Y]$. Hence this bound, $W_1 \le \tfrac{D}{2} \|\mu - \nu\|_{TV}$,
implies his Particular Case 6.16, $W_1(\mu, \nu) \le D \|\mu - \nu\|_{TV}$.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 6.15 (proof), Particular Case 6.16 and equation (6.11).
