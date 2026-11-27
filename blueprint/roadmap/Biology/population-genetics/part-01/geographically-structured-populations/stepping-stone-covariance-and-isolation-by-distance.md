# Stepping-stone covariances and isolation by distance

In the infinite one-dimensional stepping-stone model of Kimura and Weiss (1964) with demes of $N$ diploids at the integers, a fraction $m$ of immigrant gametes per generation, $m/2$ from each neighbor, and infinite-isoalleles mutation at rate $u$, let $f_k$ be the equilibrium probability that genes drawn from two demes $k$ steps apart are identical in state. To first order in the small quantities $m$, $u$ and $1/N$, the distance between the demes of two such genes falls or rises by one with probability $m$ each per generation, and identity is lost by mutation with probability $2u$, so (derivation)

$$f_k = mf_{k-1} + (1 - 2m - 2u)f_k + mf_{k+1}, \qquad k \ge 1,$$

with a separate equation for $f_0$ that carries the drift term in $1/N$. The decaying solution is proportional to $\lambda^k$ with $\lambda$ the smaller root of $m\lambda^2 - 2(m + u)\lambda + m = 0$, approximately $1 - \sqrt{2u/m}$ when $u \ll m$, so that $f_k \approx f_0\exp(-k\sqrt{2u/m})$: the one-dimensional decay law of Kimura and Weiss (1964) for the genetic correlation between colonies $k$ steps apart. In the two-dimensional model with $m/4$ from each of four neighbors, the identity at large distance along an axis behaves as $f_k \approx c\,f_0\,e^{-k\sqrt{4u/m}}/\sqrt k$ with $c$ depending on $u$ and $m$ but not on $N$ (Kimura and Weiss 1964; Weiss and Kimura 1965 show that the long-distance form of the correlation is characteristic of the dimension). In both cases $f_k/f_0$ depends on $u$ and $m$ and not on $N$, since the equations for $k \ne 0$ do not involve $N$. The decline with distance is exponential in one dimension and exponential with an additional factor $k^{-1/2}$ in two. For a finite ring of demes, see [stationary identity by descent in the circular stepping-stone model](../../infinite-alleles-model-and-homozygosity/circular-stepping-stone-model-exact-stationary-i.md).

## Depends on

- [Identity-by-descent recursion in Wright's island model](../../wright-s-island-model/island-step.md)
- [Isolation by distance](../../../coalescent-theory/structured-coalescent/isolation-by-distance.md)

## Expansion

1. The identity recursion for a general migration matrix and its reduction to the nearest-neighbor stepping-stone model.
2. The first-order difference equations and the decaying root in one dimension, with the condition $u \ll m$.
3. The two-dimensional asymptotics with the $k^{-1/2}$ factor.
4. The rates of approach to fixation without mutation in finite lines and rectangles of demes (T. Maruyama, Analysis of population structure I and II, Ann. Hum. Genet. 34 (1970), 201–219, and 35 (1971), 179–196), as a separate statement.

## Sources

- Original result: M. Kimura and G. H. Weiss, The stepping stone model of population structure and the decrease of genetic correlation with distance, Genetics 49 (1964), 561–576. <https://doi.org/10.1093/genetics/49.4.561>
- G. H. Weiss and M. Kimura, A mathematical analysis of the stepping stone model of genetic correlation, J. Appl. Probab. 2 (1965), 129–149. <https://doi.org/10.2307/3211879>
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, New York (2008). <https://doi.org/10.1007/978-0-387-78168-6>
