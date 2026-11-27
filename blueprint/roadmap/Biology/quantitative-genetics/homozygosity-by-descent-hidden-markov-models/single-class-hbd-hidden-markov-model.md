# Single-class homozygous-by-descent hidden Markov model (1R model)

Model an individual's genome along markers $m = 1,\dots,M$ (genetic distance $d_m$ Morgans between markers $m$ and $m+1$) as a two-state Markov chain $S_m \in \{1 = \text{HBD}, 2 = \text{non-HBD}\}$ with rate $R > 0$ and mixing coefficient $\rho \in (0,1)$:

$$P[S_{m+1} = 1 \mid S_m = 1] = e^{-Rd_m} + (1 - e^{-Rd_m})\rho, \qquad P[S_{m+1} = 1 \mid S_m = 2] = (1 - e^{-Rd_m})\rho,$$

$$P[S_{m+1} = 2 \mid S_m = 2] = e^{-Rd_m} + (1 - e^{-Rd_m})(1-\rho), \qquad P[S_{m+1} = 2 \mid S_m = 1] = (1 - e^{-Rd_m})(1-\rho).$$

Here $e^{-Rd_m}$ is the probability of no *coancestry change* (no recombination on either genealogical path to the common ancestor) between the markers; after a change, the new state is drawn afresh as HBD with probability $\rho$.

Emissions for a genotype $A_{mi}A_{mj}$ with allele frequencies $p_{mi}$:

$$P[A_{mi}A_{mj} \mid S_m = 1] = \begin{cases} p_{mi} & i = j,\\ 0 & i \ne j,\end{cases} \qquad P[A_{mi}A_{mj} \mid S_m = 2] = \begin{cases} p_{mi}^2 & i = j,\\ 2p_{mi}p_{mj} & i \ne j\end{cases}$$

(Hardy–Weinberg proportions in non-HBD segments).

**Properties.** The stationary distribution of the chain is $(\rho, 1-\rho)$, so $\rho$ is the expected proportion of the genome HBD (the genomic inbreeding coefficient). HBD segments without a coancestry change have exponential length with mean $1/R$; the number of consecutive HBD segments in a run is geometric with parameter $1-\rho$, so IBD tracts have mean length $1/\{R(1-\rho)\}$. The likelihood is computed by the forward algorithm and maximized numerically in $(R,\rho)$.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

Write the transition matrix as $e^{-Rd}I + (1-e^{-Rd})\mathbf 1\pi^\top$ with $\pi = (\rho, 1-\rho)^\top$; then $\pi^\top P = e^{-Rd}\pi^\top + (1-e^{-Rd})\pi^\top = \pi^\top$. A run of HBD markers ends only at a coancestry change followed by a non-HBD draw, which gives the geometric number of segments and the tract mean $\sum_{k\ge1}k(1-\rho)\rho^{k-1}/R = 1/\{R(1-\rho)\}$.

## Sources

- Tom T. Druet and Mathieu Gautier, "A hidden Markov model to estimate homozygous-by-descent probabilities associated with nested layers of ancestors", Theoretical Population Biology (2022), <https://doi.org/10.1016/j.tpb.2022.03.001>. bioRxiv 10.1101/2021.05.25.445246. Section 2.1.1, Eqs. (1)–(3) (model of Leutenegger et al., Am. J. Hum. Genet. 2003).
