# Gene tree density under the multispecies coalescent with branch population functions

Let $S$ be a rooted [species tree](species-tree.md) with divergence times, in which every branch $b$
(extant or ancestral species) exists over a time interval $[\sigma_b, \sigma'_b)$, measured backward
from the present, with $\sigma'_b < \infty$ except for the root branch, whose interval is
$[\sigma_{\mathrm{root}}, \infty)$. Each branch carries a measurable population size function
$N_b : [\sigma_b, \sigma'_b) \to (0, \infty)$ whose reciprocal is integrable on every bounded interval
$[\sigma_b, u]$ with $u < \sigma'_b$, and on the root branch the cumulative pair rate diverges:

$$\int_{\sigma_{\mathrm{root}}}^{\infty} \frac{dt}{N_{\mathrm{root}}(t)} = \infty .$$

Gene lineages, sampled from one or more individuals per extant species, evolve as follows: inside each
branch every pair of lineages present at time $t$ coalesces at rate $1/N_b(t)$, independently of
everything outside the branch, and the lineages still present at $\sigma'_b$ pass to the parent branch.
The divergence of the root-branch pair rate makes the lineages coalesce to one ancestor almost surely.

Let $g$ be a rooted gene tree on the sampled lineages with coalescence times, embedded in $S$: each
lineage of $g$ lies inside one branch of $S$ at every time, and coalescences happen only between
lineages in the same branch. For a branch $b$ let $l$ be the number of lineages of $g$ entering $b$ at
$t_0 = \sigma_b$, let $t_0 < t_1 < \dots < t_k < t_{k+1} = \sigma'_b$ be the times of the $k$
coalescences of $g$ inside $b$, and let $\pi_i$ be the pair of lineages of $g$ that merges at $t_i$.
Thus $l - i$ lineages are present on $(t_i, t_{i+1})$ and $l - k$ leave $b$; on the root branch
$t_{k+1} = \infty$ and $l - k = 1$. Write $H_b(g) = \bigl(l, (t_0, \dots, t_{k+1}), (\pi_1, \dots, \pi_k)\bigr)$
for this lineage history, which records which pair merges at each event. The likelihood contribution
of the specified genealogy on $b$ is

$$P\bigl(H_b(g) \mid N_b\bigr) = \prod_{i=1}^{k} \frac{1}{N_b(t_i)} \ \prod_{i=0}^{k} Q_i,$$

with survival factors

$$Q_i = \exp\Bigl(-\binom{l-i}{2}\int_{t_i}^{t_{i+1}} \frac{dt}{N_b(t)}\Bigr) \quad \text{if } l - i \ge 2, \qquad Q_i = 1 \quad \text{if } l - i = 1 .$$

The factor $Q_k$ is the probability of no further coalescence before the branch ends; once one lineage
remains it is $1$, including on the infinite root branch. The density of the gene tree $g$, with respect
to counting measure on its labelled topology and Lebesgue measure on its coalescence times, is the
product over the branches of $S$,

$$P(g \mid S) = \prod_{b \in S} P\bigl(H_b(g) \mid N_b\bigr),$$

and $P(g \mid S) = 0$ for a gene tree that cannot be embedded in $S$. The density of the lineage
counts and event times alone, forgetting which pairs merged, differs: its $i$-th event in $b$ carries
the rate $\binom{l-i+1}{2}/N_b(t_i)$ of some merger among the $l - i + 1$ lineages present, rather than
$1/N_b(t_i)$; those pair-count factors belong to the times-only density, not to $P(g \mid S)$.

With constant sizes $N_b(t) \equiv c_b > 0$ the hypotheses hold and the integrals become
$(t_{i+1} - t_i)/c_b$. An alternative model takes $N_b$ linear on each branch with continuity at
splits: the sizes of the two daughter species at their divergence add up to the size of the ancestral
species; a linear size $a + c\,(t - \sigma_{\mathrm{root}})$ with $a > 0$ and $c \ge 0$ on the root
branch still has a divergent reciprocal integral.

## Depends on

- [Rooted binary species tree with branch lengths](species-tree.md)

## Proof depends on

- [Holding times and jump chain of Kingman's n-coalescent are independent](../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)

## Expansion

Inside one branch the genealogy is Kingman's coalescent run on the time-changed clock
$\Lambda_b(t) = \int_{t_0}^{t} ds / N_b(s)$, which is finite and continuous for $t < \sigma'_b$ because
$1/N_b$ is locally integrable. In clock units, with $m$ lineages present the holding time is
exponential with rate $\binom{m}{2}$ and, independently, the merging pair is uniform among the
$\binom{m}{2}$ pairs, so a specified pair merging at clock time $\Lambda_b(t_i)$ has density
$\exp\bigl(-\binom{m}{2}\,\Delta\Lambda\bigr)$ in $\Lambda$; the change of variables
$d\Lambda_b = dt / N_b(t)$ contributes $1/N_b(t_i)$, and each interval contributes its survival
probability. Branches are conditionally independent given the lineages crossing their ends, which yields
the product over branches. On the root branch $\Lambda_{\mathrm{root}}(t) \to \infty$, so the
time-changed coalescent reaches one lineage almost surely and the law is a probability law. Gene
lineages that fail to coalesce in a branch pass to the parent branch, the source of incomplete lineage
sorting and of discordance between gene trees and species trees.

## Sources

- J. Heled, A. J. Drummond, "Bayesian inference of species trees from multilocus data", Molecular
  Biology and Evolution 27 (2010) 570-580, Methods, "Computing the Multispecies Coalescent",
  Eqs. (2) and (3), <https://doi.org/10.1093/molbev/msp274> (PMC2822290).
