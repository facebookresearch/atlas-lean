# Greedy adaptation versus valley crossing in the sequential-fixation regime

Consider an asexual population of constant size $N$ at a wild-type genotype $w$ that can reach two fitter states: an immediately beneficial "uphill" genotype $u$ of selective advantage $s_u > 0$, reached by one mutation at rate $\mu_u$ per individual per generation, and a doubly mutant "valley-crossing" genotype $v$ of advantage $s_v > s_u$, reached only through an intermediate $i$ of fitness effect $-\delta_i \le 0$, with mutation rates $\mu_i$ from $w$ to $i$ and $\mu_v$ from $i$ to $v$. Assume weak selection, $s_j \ll 1$ for all genotypes, and let the uphill genotype be an evolutionary dead end.

When $N$ is small enough that the population is nearly clonal, it moves in Markovian jumps between neighbouring genotypes, with transition rate

$$r_{jk} = N \mu_{jk} \pi_{jk}, \qquad \pi_{jk} = \frac{1 - e^{-2(s_k - s_j)}}{1 - e^{-2N(s_k - s_j)}},$$

$\pi_{jk}$ being the fixation probability of a single $k$ mutant in a population of $j$. Treating $w$ and $i$ as transient states and $u$ and $v$ as absorbing, and allowing back-mutation from a fixed intermediate to the wild type, the probability that the population ends at the doubly mutant genotype rather than at the uphill genotype is

$$P_{\mathrm{cross}} = \frac{r_{wi} r_{iv}}{r_{wi} r_{iv} + r_{wu}(r_{iw} + r_{iv})} = \left[ 1 + \frac{\pi_{wu}}{\pi_{wi}} \frac{\mu_u}{\mu_i} \left( 1 + \frac{\mu_i \pi_{iw}}{\mu_v \pi_{iv}} \right) \right]^{-1}.$$

Within this regime $P_{\mathrm{cross}}$ **decreases** with $N$: as $N$ grows, $\pi_{wu} \to 2 s_u$ while $\pi_{wi} \to 0$ for a deleterious intermediate, so the ratio $\pi_{wu}/\pi_{wi} \to \infty$ and $P_{\mathrm{cross}} \to 0$. Larger populations are the greedier ones, until stochastic tunneling takes over: the sequential-fixation description fails once

$$N > \frac{1}{2\delta_i} \log\!\left( 1 + \frac{e^{2\delta_i} - 1}{p_v} \right),$$

where $p_v = -\delta_i + \sqrt{\delta_i^2 + 4 \mu_v s_v}$ is the probability that an intermediate lineage survives drift long enough to produce a successful double mutant.

## Depends on

- [Kimura's fixation probability](../../diffusion-theory/wright-fisher-diffusion/kimura-fixation.md)
- [Haldane's 2s approximation holds in the joint regime](../../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/tendsto-kimura-fixation-div-two-mul.md)
- [Absorption probabilities and mean times of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Expansion

In the clonal regime each genotype is either absent or fixed, and the waiting time to each transition is exponential with rate equal to the population-wide mutation supply times the fixation probability, which gives the absorbing Markov chain. The absorption probabilities follow from first-step analysis: from $w$ the chain goes to $u$ with relative weight $r_{wu}$ and to $i$ with weight $r_{wi}$, and from $i$ it either returns to $w$ (weight $r_{iw}$) or completes the crossing (weight $r_{iv}$). The role of the uphill genotype here is to impose a deadline on an otherwise homogeneous Poisson process of valley crossing: once an uphill mutation destined to fix appears, it sweeps quickly and the wild type, with it the supply of intermediates, is lost. The nonmonotonicity of $P_{\mathrm{cross}}$ in $N$ is the main qualitative consequence: intermediate-size populations are the most greedy, while both smaller populations (which fix deleterious intermediates by drift) and much larger ones (which tunnel) are more likely to reach the distant, fitter genotype. Limits of the derivation: $p_v$ and the fixation probabilities assume weak selection, and the formula excludes clonal interference among multiple competing uphill mutations.

## Sources

- I. E. Ochs, M. M. Desai, "The competition between simple and complex evolutionary trajectories in asexual populations", *BMC Evolutionary Biology* 15 (2015), 55, <https://doi.org/10.1186/s12862-015-0334-0> (PMC4391547). Results, "Sequential fixation" and "Stochastic tunneling", Equations (1)–(4) and (16)–(17).
