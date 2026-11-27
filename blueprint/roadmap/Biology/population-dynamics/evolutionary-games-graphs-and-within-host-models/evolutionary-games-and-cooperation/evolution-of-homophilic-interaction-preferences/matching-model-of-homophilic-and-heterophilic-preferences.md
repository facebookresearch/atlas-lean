# Matching model of homophilic and heterophilic preferences

Let a haploid asexual population of size $N$ consist of individuals $i$ with an observable phenotype $G_i \in \{1, \dots, M\}$ and a heritable **preference** $p_i \in [0,1]$, the probability of seeking a partner of the individual's own phenotype. Phenotypes carry no intrinsic fitness; only the combination of the two partners' phenotypes pays. An interaction yields the **homophilic payoff** $a$ when $G_i = G_j$ and the **heterophilic payoff** $b$ when $G_i \ne G_j$, and non-interaction yields $0$. An encounter between $i$ and $j$ becomes an actual interaction only if both partners sought a partner of the type the other offers, so, with the two choices independent, the probability of a successful interaction is

$$\Pr[\text{interact}] = \begin{cases} p_i\,p_j, & G_i = G_j, \\ (1 - p_i)(1 - p_j), & G_i \ne G_j. \end{cases}$$

Writing $\delta_{ij} = \mathbf 1[G_i = G_j]$, the expected payoff of one encounter is

$$\pi_{ij} = \delta_{ij}\, p_i p_j\, a + (1 - \delta_{ij})(1 - p_i)(1 - p_j)\, b ,$$

and an individual's expected payoff is the average of $\pi_{ij}$ over the composition of the population. Three regimes follow from the payoffs alone: $a > b$ rewards homophilic interactions (synergy), $a < b$ rewards heterophilic ones (specialisation), and $a = b$ favours neither. Preferences and phenotypes then evolve together in a frequency-dependent Moran process in which fitness is an exponential function of the average payoff and offspring mutate their preference or phenotype with small probability.

## Depends on

- [Fixation probability in a frequency-dependent Moran process](../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)

## Remarks

Because an interaction requires mutual consent, the payoff is quadratic in the preferences rather than linear: raising $p_i$ helps only in proportion to how often partners of the same phenotype also raise theirs, so the preference trait experiences positive frequency dependence even when $a$ and $b$ are fixed. A homophilic preference also guarantees a partner whenever one's own phenotype is common, while a heterophilic preference becomes self-defeating as it spreads, since partners that would accept it grow rare; this asymmetry is the mechanism by which Fu, Nowak, Christakis and Fowler find homophily evolving over a wide range of conditions, including some with $a < b$. The same framework is used to read empirical association data, where estimated average preferences across several species and phenotypes fall between $0.53$ and $0.68$, all above the indifference value $p = 1/2$.

## Sources

- F. Fu, M. A. Nowak, N. A. Christakis, J. H. Fowler, "The evolution of homophily", Scientific Reports 2 (2012), 845, <https://doi.org/10.1038/srep00845> (PMC3496167), Model section and Results, Table 1.
