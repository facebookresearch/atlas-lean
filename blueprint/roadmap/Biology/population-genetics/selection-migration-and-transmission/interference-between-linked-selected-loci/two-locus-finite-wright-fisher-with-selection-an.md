# A finite haploid selection–recombination Wright–Fisher chain

Fix an integer $M\ge1$, positive haplotype fitnesses $w_g$ for
$g\in\{AB,Ab,aB,ab\}$ and $r\in[0,1/2]$.
The state space is the four-part compositions $n$ of $M$, with
$x_g=n_g/M$. First use canonical [haploid selection](../../natural-selection-fisher-s-theorem-and-the-price/select.md)
to form $y_g=x_gw_g/\sum_hx_hw_h$. Then use canonical
[recombination](../../linkage-disequilibrium-and-haldane-s-map-functio/recombine.md)
to form $p_{ab}=(1-r)y_{ab}+r(\sum_vy_{av})(\sum_uy_{ub})$.
Equivalently $p_g=y_g-e_grD(y)$ with $e=(1,-1,-1,1)$.
Finally draw the next composition $m$ by $M$ independent categorical
trials with probabilities $p$:

$$P(n,m)=\frac{M!}{\prod_gm_g!}\prod_gp_g^{m_g},
\qquad m_g\ge0,\quad\sum_gm_g=M,$$

using $0^0=1$. These are nonnegative numbers summing to one, so this
defines a finite Markov chain. There is no mutation in this model.
With equal fitnesses each single-locus allele-count process, with respect
to the full chain's history, has the canonical
[neutral Wright–Fisher transition kernel](../../wright-fisher-markov-chain/wright-fisher.md).

## Depends on

- [Haploid selection](../../natural-selection-fisher-s-theorem-and-the-price/select.md)
- [Random mating with recombination](../../linkage-disequilibrium-and-haldane-s-map-functio/recombine.md)
- [Neutral Wright–Fisher kernel](../../wright-fisher-markov-chain/wright-fisher.md)

## Expansion

Positive mean fitness makes $y$ a probability vector, and the convex
recombination expression makes $p$ a probability vector. The multinomial
theorem gives each row sum as $(\sum_gp_g)^M=1$.
Recombination preserves each allele marginal. Under equal fitnesses,
$y=x$, so conditional on the complete past the next $A$ count is
$\operatorname{Binomial}(M,n_A/M)$, and likewise for $B$.
The two locus-count processes need not be independent of one another.
The finite sampling kernel is built from [haploid selection](../../natural-selection-fisher-s-theorem-and-the-price/select.md) and
[recombination](../../linkage-disequilibrium-and-haldane-s-map-functio/recombine.md), not from the different diploid
viability-selection/meiosis recursion.

## Sources

- J. Felsenstein, "The evolutionary advantage of recombination", Genetics 78 (1974), 737–756, <https://doi.org/10.1093/genetics/78.2.737>.
