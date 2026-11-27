# Gene-tree density under the multispecies coalescent with introgression

An **MSci model** is a rooted species network obtained from a species tree by adding hybridization nodes $H$, each with one daughter population and two parental populations $H_l$ and $H_r$. The node and its parents may share an age, which covers admixture and horizontal transfer. The parameters are the node ages $\tau$, the population-size parameters $\theta = 4N\mu$ of all populations (both measured in expected mutations per site), and an introgression probability $\varphi_H \in (0,1)$ for each $H$. Tracing a lineage backward in time, at $H$ it enters $H_l$ with probability $\varphi_H$ and $H_r$ with probability $1 - \varphi_H$, independently of other lineages. Within each population, lineages coalesce as in Kingman's coalescent at rate $2/\theta$ per pair.

A gene tree $G_i$ at locus $i$ consists of its topology, its coalescence times, and for every branch a flag at each hybridization node it crosses ($l$, $r$, or $\varnothing$ if it does not pass that node). Its density factorizes over populations and hybridization nodes:

$$f(G_i \mid \tau, \theta, \varphi) = \prod_{H} \varphi_H^{\,n_{H,l}} (1 - \varphi_H)^{\,n_{H,r}} \prod_{\text{populations } P}\ \prod_{j} \Bigl(\frac{2}{\theta_P}\Bigr)^{\delta_{P,j}} \exp\Bigl(-\frac{k_{P,j}(k_{P,j}-1)}{\theta_P}\,\Delta t_{P,j}\Bigr),$$

where $n_{H,l}$ and $n_{H,r}$ count the gene-tree lineages taking the left and right parents at $H$. Inside population $P$ the history is cut into consecutive intervals of length $\Delta t_{P,j}$ with $k_{P,j}$ lineages, and $\delta_{P,j} = 1$ if the interval ends with a coalescence (else it ends at the population's upper boundary).

Assuming free recombination between loci, no recombination within a locus, and sequence likelihood $f(X_i \mid G_i)$ under a substitution model, the posterior over the network parameters is

$$f(\tau, \theta, \varphi \mid X) \propto f(\tau, \theta, \varphi) \prod_{i=1}^{L} \int f(G_i \mid \tau, \theta, \varphi)\, f(X_i \mid G_i)\, dG_i, \tag{1}$$

with inverse-gamma priors on $\theta$ and $\tau$ and beta priors on $\varphi$. It is sampled by MCMC over gene trees and parameters, and the gene-tree moves resample the flags whenever a node age or attachment point changes.

## Proof depends on

- [Gene tree density under the multispecies coalescent with branch population functions](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md)

## Proof sketch

Given the flags, every gene-tree branch has a definite path through the network. The network then acts as a species tree whose populations are entered by known sets of lineages, so the multispecies-coalescent density applies population by population. During an interval with $k$ lineages in a population of size $\theta$, the waiting time to the next coalescence is exponential with rate $k(k-1)/\theta$. A coalescence contributes the rate $2/\theta$ of the specific pair that merges, and an interval reaching the population's top contributes only the survival factor. The flags are Bernoulli($\varphi_H$) choices, which gives the product of $\varphi_H$ powers. The data inform $\varphi$ only through this factor, so a $\varphi$ update leaves the sequence likelihood unchanged. Without hybridization nodes the density reduces to the Rannala–Yang multispecies coalescent density.

## Depends on

- [The multispecies coalescent as a constructed process](msc-realization-gene-tree-probability-equals-the.md)

## Sources

- T. Flouri, X. Jiao, B. Rannala and Z. Yang, "A Bayesian implementation of the multispecies coalescent model with introgression for phylogenomic analysis", Molecular Biology and Evolution (2020; online 2019), Results ("The MSci Model", Equation (1)) and Materials and Methods ("MCMC Proposals", Steps 1–6), <https://doi.org/10.1093/molbev/msz296>, PMCID PMC7086182.
