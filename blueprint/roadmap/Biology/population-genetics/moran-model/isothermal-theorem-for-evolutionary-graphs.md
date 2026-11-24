# Fixation probability on isothermal graphs

In the model of Lieberman, Hauert and Nowak (2005), $N$ individuals occupy the vertices of a graph with weights $w_{ij}$, $\sum_j w_{ij} = 1$; at each step an individual $i$ is chosen to reproduce with probability proportional to its fitness (mutant $r$, resident $1$) and its offspring replaces $j$ with probability $w_{ij}$. The temperature of vertex $i$ is $T_i = \sum_j w_{ji}$, and a vertex is hot if it is replaced often and cold if rarely. For $r > 0$, $r \ne 1$, write $\rho_1(r) = (1 - 1/r)/(1 - 1/r^N)$ for the Moran fixation probability of a single mutant. The paper states the isothermal theorem as an equivalence quantified over all mutant fitnesses: the fixation probability of a single mutant placed at a uniformly random vertex equals $\rho_1(r)$ for every $r \ne 1$ if and only if all vertices have the same temperature, which is equivalent to $W$ being doubly stochastic; more generally it equals $\rho_1(r)$ for every $r \ne 1$ if and only if the weighted graph is a circulation. The case $r = 1$ is separate: $\rho_1$ is not defined there, and on every finite graph on which fixation or extinction occurs almost surely the neutral fixation probability of a randomly placed mutant is $1/N$, isothermal or not, because the fixation probabilities of the $N$ initial lineages sum to $1$. The paper further states that one-rooted graphs give fixation probability $1/N$ for every $r$, and that the star amplifies selection: its fixation probability is given for large $N$ by $\rho_2 = (1 - 1/r^2)/(1 - 1/r^{2N})$, whose limit as $N \to \infty$ for $r > 1$ is $1 - 1/r^2$, against $1 - 1/r$ for $\rho_1$; the precise asymptotic form is part of the target. Later work examines the limits of the isothermal theorem: Kaveh, Komarova and Kohandel (2015) note that it is proved for birth–death updating with mutants differing in birth rate, show that for death–birth updating it holds only for mutants that differ in death rate, and show that for more general birth and death rates fixation probabilities on such graphs differ from those of the well-mixed population.

## Depends on

- [Fixation probability of the Moran process](../../../Biology/population-genetics/moran-model/moran-fixation.md)

## Expansion

1. The model: the birth–death process on a weighted graph and the [Moran fixation probability](../../../Biology/population-genetics/moran-model/moran-fixation.md).
2. The "if" direction: when $W$ is doubly stochastic the number of mutants is itself a birth–death chain with the Moran transition ratio $r$, hence has fixation probability $\rho_1(r)$ from a single randomly placed mutant, for every $r \ne 1$. The neutral case $r = 1$, with value $1/N$ on every graph on which fixation or extinction is certain.
3. The converse and the circulation generalization, each as a separate statement with the precise hypotheses.
4. One-rooted graphs, and the star and super-star amplifiers with the asymptotic statement for the star in the form $\lim_{N \to \infty}$ of its fixation probability, fixed from the source.
5. Death–birth updating and the limits of the isothermal theorem; relation to [the minimum fixation probability on graphs](../../../Biology/population-genetics/moran-model/minimum-fixation-probability-on-graphs.md).

## Sources

- E. Lieberman, C. Hauert and M. A. Nowak, Evolutionary dynamics on graphs, Nature 433 (2005), 312–316. <https://doi.org/10.1038/nature03204>
- K. Kaveh, N. L. Komarova and M. Kohandel, The duality of spatial death–birth and birth–death processes and limitations of the isothermal theorem, 2015. <https://arxiv.org/abs/1411.4556>
