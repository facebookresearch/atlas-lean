# Gene tree density under the multispecies coalescent with branch population functions

Let $S$ be a rooted [species tree](species-tree.md) with divergence times, in which every branch $b$
(extant or ancestral species) exists over a time interval and carries a positive, integrable
population size function $N_b(t)$. Let $g$ be a rooted gene tree with coalescence times, sampled from
one or more individuals per extant species and embedded in $S$: each lineage of $g$ lies inside one
branch of $S$ at every time, lineages pass from a branch to its parent at the divergence time, and
coalescences happen only between lineages in the same branch. Assume that, within each branch, every
pair of lineages present coalesces at rate $1/N_b(t)$ at time $t$ (time measured backward from the
present), independently of everything outside the branch.

For a branch $b$ with start and end times $t_0 < t_{k+1}$ (backward in time), let $l$ be the number of
gene lineages entering $b$ at $t_0$, and let $t_0 < t_1 < \dots < t_k < t_{k+1}$ be the times of the $k$
coalescences of $g$ inside $b$, so that $l - i$ lineages are present on $(t_i, t_{i+1})$ and $l - k$
lineages leave $b$ at $t_{k+1}$. Write $L_b(g) = \{l, (t_0, \dots, t_{k+1})\}$ for this lineage history.
Its density is

$$P\bigl(L_b(g) \mid N_b\bigr) = \prod_{i=1}^{k} \frac{1}{N_b(t_i)}
\ \prod_{i=0}^{k} \exp\Bigl(-\binom{l-i}{2}\int_{t_i}^{t_{i+1}} \frac{dt}{N_b(t)}\Bigr),$$

where the last factor ($i = k$) is the probability of no further coalescence before the branch ends.
For the root branch $t_{k+1} = \infty$ and $l - k = 1$. The density of the whole gene tree is the
product over the branches of $S$,

$$P(g \mid S) = \prod_{b \in S} P\bigl(L_b(g) \mid N_b\bigr).$$

With constant sizes $N_b(t) \equiv c_b$ the integrals become $(t_{i+1} - t_i)/c_b$. An alternative
model takes $N_b$ linear on each branch with continuity at splits: the sizes of the two daughter
species at their divergence add up to the size of the ancestral species.

## Depends on

- [Rooted binary species tree with branch lengths](species-tree.md)

## Expansion

Inside one branch the genealogy is Kingman's coalescent run on a time-changed clock
$\Lambda_b(t) = \int dt / N_b(t)$: with $m$ lineages present the waiting time to the next coalescence
has hazard $\binom{m}{2}/N_b(t)$, so each observed event contributes the hazard of the specific pair
that merges, $1/N_b(t_i)$, and each interval contributes its survival probability. Branches are
conditionally independent given the numbers of lineages crossing their ends, which yields the
product over branches. Gene lineages that fail to coalesce in a branch pass to the parent branch,
the source of incomplete lineage sorting and of discordance between gene trees and species trees.

## Sources

- J. Heled, A. J. Drummond, "Bayesian inference of species trees from multilocus data", Molecular
  Biology and Evolution 27 (2010) 570-580, Methods, "Computing the Multispecies Coalescent",
  Eqs. (2) and (3), <https://doi.org/10.1093/molbev/msp274> (PMC2822290).
