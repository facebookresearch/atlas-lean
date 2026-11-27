# Two-compartment branching-process model of a drug sanctuary

Cells have genotype $i \in \{0, 1\}$ (sensitive, resistant) and location $j \in \{0, 1\}$ (sanctuary compartment $0$ and drug-exposed compartment $1$, with drug concentrations $D_0 < D_1$). A cell of type $ij$ divides at rate

$$b_{ij} = \frac{\beta_j (1 - i s)}{1 + \big(D_j / (\rho^{i}\, \mathrm{IC}_{50})\big)^{m}},$$

dies at rate $d_{ij} = \alpha_j$ and migrates to the other compartment at rate $v$; here $\beta_j, \alpha_j$ are drug-free birth and death rates, $s \in [0,1)$ the cost of resistance, $\rho > 1$ the fold increase of $\mathrm{IC}_{50}$ conferred by the resistance mutation and $m > 0$ the Hill coefficient (the drug is cytostatic). At each division of a sensitive cell one daughter becomes resistant with probability $u$. Cells act independently, so the population is a four-type continuous-time Markov branching process. With $X = (x_{00}, x_{01}, x_{10}, x_{11})$ and $F_{ij}(X; t)$ the probability generating function of the population at time $t$ descended from one $ij$ cell, the backward equations are

$$\begin{aligned}
\partial_t F_{00} &= d_{00} + b_{00}(1-u) F_{00}^2 + b_{00} u F_{00} F_{10} + v F_{01} - (d_{00} + b_{00} + v) F_{00},\\
\partial_t F_{01} &= d_{01} + b_{01}(1-u) F_{01}^2 + b_{01} u F_{01} F_{11} + v F_{00} - (d_{01} + b_{01} + v) F_{01},\\
\partial_t F_{10} &= d_{10} + b_{10} F_{10}^2 + v F_{11} - (d_{10} + b_{10} + v) F_{10},\\
\partial_t F_{11} &= d_{11} + b_{11} F_{11}^2 + v F_{10} - (d_{11} + b_{11} + v) F_{11},
\end{aligned}$$

with $F_{ij}(X; 0) = x_{ij}$. Starting from one sensitive cell in compartment $j$, the probability of having no resistant cell at time $t$, conditioned on the lineage not going extinct without producing resistance, is

$$p_s(t) = \frac{F_{0j}(1,1,0,0;t) - F_{0j}(1,1,0,0;\infty)}{1 - F_{0j}(1,1,0,0;\infty)},$$

and the mean time to resistance (relapse time) is $\bar T_r = \int_0^\infty p_s(\tau)\, d\tau$.

## Expansion

The backward equations follow from a first-step decomposition over the first event of the founding cell: death (contributing the constant $d_{ij}$), division into two identical daughters, division producing a resistant daughter (sensitive cells only), or migration, each weighted by its rate, minus the total event rate times $F_{ij}$. Setting $x_{00} = x_{01} = 1$ and $x_{10} = x_{11} = 0$ evaluates the probability that no resistant cell is present at time $t$; the limit $t \to \infty$ is the probability of extinction before resistance appears, which is why it is removed in $p_s$. The joint law of resistant counts in the two compartments is extracted from $F_{0j}(1,1,x,y;t)$ by Cauchy's integral formula on the unit circles, discretized as a two-dimensional discrete Fourier transform of the generating function. The model extends to $n$ resistance mutations and $M$ compartments with ring (local) or all-to-all (global) migration.

## Sources

- F. Fu, M. A. Nowak and S. Bonhoeffer, "Spatial heterogeneity in drug concentrations can facilitate the emergence of resistance to cancer therapy", PLoS Computational Biology 11 (2015), e1004142, <https://doi.org/10.1371/journal.pcbi.1004142> (PMC4366398). Materials and Methods, Equations (3)-(7).
