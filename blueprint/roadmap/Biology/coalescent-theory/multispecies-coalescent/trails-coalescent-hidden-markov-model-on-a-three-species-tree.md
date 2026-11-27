# TRAILS coalescent hidden Markov model on a three-species tree

**Species tree and parameters.** Three species $A$, $B$, $C$ with species tree $((A, B), C)$ and an outgroup $D$ are sampled with one haploid sequence each. Backwards in time, the $A$ and $B$ lineages stay isolated until the first speciation time ($t_A$, $t_B$ from the present), then share the ancestral population $AB$ of effective size $N_{AB}$ for a further time $t_2$, after which the $C$ lineage joins and all three lineages share the ancestral population $ABC$ of size $N_{ABC}$. The recombination rate is $\rho$ per site per generation; the mutation rate is fixed to $1$ and all times and sizes are expressed in mutation units, because only these ratios are identifiable.

**Ancestral process for two adjacent sites.** For one sequence, the left and right sites are either linked or unlinked; with recombination rate $\rho_1$ and re-joining (coalescence of the two sites' ancestors) rate $\gamma_1$, the rate matrix on (unlinked, linked) is

$$Q_1 = \begin{pmatrix} -\gamma_1 & \gamma_1 \\ \rho_1 & -\rho_1 \end{pmatrix}.$$

For two sequences the two-site coalescent with recombination is a continuous-time Markov chain with $15$ states and two absorbing states (both sites fully coalesced); for three sequences it has $203$ states. Within each segment of the species tree the appropriate chain runs for the length of that segment; at a speciation the end-of-segment distributions of the merging lineages are combined into the initial distribution of the chain with more sequences.

**Hidden states.** A hidden state is a rooted three-leaf gene tree: a topology together with the discretized time intervals of its two coalescences. Time is cut into $n_{AB}$ intervals between the two speciations and $n_{ABC}$ intervals in the $ABC$ ancestor. States whose first coalescence joins $A$ and $B$ inside $AB$ are concordant; states whose first coalescence lies in $ABC$ carry any of the three topologies, each equally likely a priori, two of which are discordant (incomplete lineage sorting).

**Transitions and emissions.** The probability of the hidden-state pair at two adjacent sites is obtained by summing the absorbing paths of the interconnected chains consistent with both gene trees and their time intervals; dividing by the single-site marginal gives the transition matrix of the hidden Markov model. Emissions are four-way alignment columns ($A, B, C$ and the outgroup $D$), computed for each hidden state under the Jukes–Cantor substitution model, so recurrent mutation is allowed. Parameters are fitted by maximizing the forward-algorithm likelihood, and posterior decoding gives per-site posterior probabilities of topologies and coalescence intervals, i.e. a decoded ancestral recombination graph of the three sequences.

**Incomplete lineage sorting.** With $N_{AB}$ haploid individuals in the $AB$ ancestor (pair coalescence rate $1/N_{AB}$ per generation), the probability that a site's gene tree is discordant with the species tree is

$$\Pr(\mathrm{ILS}) = \tfrac23\, e^{-t_2/N_{AB}},$$

equivalently $\tfrac23 e^{-t_2/(2N)}$ for $N$ diploid individuals; each discordant topology has probability $\tfrac13 e^{-t_2/N_{AB}}$.

## Depends on

- [Probability of the discordant three-species gene tree with cherry $\{0, 2\}$](gene-tree-prob-triple-cherry-02.md)
- [Three-species concordance](gene-tree-prob-triple-matching.md)
- [The multispecies coalescent](gene-tree-prob.md)
- [Coalescent with recombination: ancestral-material state space and generator](../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md)
- [Jukes–Cantor transition probability](../../phylogenetics/jukes-cantor-model/jc-prob.md)

## Expansion

With $n_{AB} = n_{ABC} = 1$ the state space collapses to the four genealogies of CoalHMM (one concordant state with coalescence in $AB$, and three states with both coalescences in $ABC$), whose estimates of $t_2$, $N_{AB}$ and $\rho$ are biased because coalescence times within a branch are not modelled; refining the time grid removes most of this bias in simulations. Conditional on ILS the deeper coalescence time is a sum of exponentials of rates $3$ and $1$ in coalescent units, while conditional on the concordant state with first coalescence in $AB$ it is exponential of rate $1$ after entering $ABC$, which explains why windows rich in ILS also have older coalescences. Excess posterior mass of coalescences in one ancestral interval relative to the neutral expectation flags ancient selective sweeps. Allowing $t_A$, $t_B$ and the $C$ tip length to differ fits non-ultrametric trees (branch-specific mutation-rate or generation-time differences).

## Sources

- I. Rivas-González, M. H. Schierup, J. Wakeley and A. Hobolth, "TRAILS: Tree reconstruction of ancestry using incomplete lineage sorting", PLoS Genetics 20 (2024), e1010836, Methods ("Continuous-time Markov chains for the ancestral process", Eq. (1); "Transition probabilities of the HMM"; "Emission probabilities of the HMM"; "Parameterization") and Results ("Parameter estimation from a HCGO alignment", ILS formula), <https://doi.org/10.1371/journal.pgen.1010836>, PMCID PMC10880969.
