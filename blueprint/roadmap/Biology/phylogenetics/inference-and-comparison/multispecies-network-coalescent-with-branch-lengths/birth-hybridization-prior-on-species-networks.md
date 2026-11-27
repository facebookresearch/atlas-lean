# Birth–hybridization prior on species networks

The **birth–hybridization process** with speciation rate $\lambda > 0$, hybridization rate $\nu \ge 0$ and time of origin $t_0 > 0$ generates a rooted, time-calibrated species network forward in time from $t_0$ to the present ($t = 0$):

- start with a single lineage at time $t_0$;
- when $k$ lineages are present, the next event occurs after an exponential waiting time with total rate

$$r_{\mathrm{tot}}(k) = k \lambda + \binom{k}{2} \nu ;$$

- the event is a speciation with probability $k\lambda / r_{\mathrm{tot}}(k)$, in which case a uniformly chosen lineage splits into two, and otherwise a hybridization, in which case a uniformly chosen pair of lineages merges into one hybrid lineage, creating a reticulation node with inheritance probability $\gamma \sim \mathrm{U}(0, 1)$ (or another law on $[0, 1]$);
- the process stops at time $0$; the extant lineages are the tips.

The induced law of the network (topology, node times, inheritance probabilities), conditioned if desired on the number of tips, serves as the prior $f(\Psi \mid \lambda, \nu, t_0)$ in Bayesian inference of species networks.

Properties:

- with $\nu = 0$ the process is the pure-birth (Yule) process and generates species trees;
- the lineage count is a continuous-time Markov chain on $\{1, 2, \dots\}$ with up-rate $k\lambda$ and down-rate $\binom{k}{2}\nu$; because the down-rate grows quadratically, hybridizations dominate at large $k$, so an informative prior keeping $\nu$ below $\lambda$ (for example $r = \nu/\lambda \sim \mathrm{U}(0, 1)$ and an exponential prior on the net rate $d = \lambda - \nu$) prevents networks from growing beyond what gene trees can distinguish;
- networks may contain parallel branches (two edges between the same pair of nodes), which arise naturally from incomplete sampling.

## Expansion

Competing exponential clocks give the total rate as the sum of $k$ speciation clocks and $\binom{k}{2}$ pairwise hybridization clocks, and the probability that a speciation fires first is the ratio of its rate to the total. The prior is used jointly with the gene-tree density and the per-locus sequence likelihoods in a posterior over networks, embeddings, gene trees and rates; matching summary statistics (network length, root height, number of hybridizations) between direct simulation of the process and MCMC sampling without data was used to validate the implementation. Analogues of birth–death extensions (extinction, incomplete sampling, time-varying rates) can be added to the prior.

## Sources

- C. Zhang, H. A. Ogilvie, A. J. Drummond and T. Stadler, "Bayesian inference of species networks from multilocus sequence data", Molecular Biology and Evolution 35 (2018), sections on the species network prior and "Simulation and MCMC Sampling without Sequence Data", <https://doi.org/10.1093/molbev/msx307> (PMC5850812).
