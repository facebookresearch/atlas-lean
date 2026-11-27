# Discrete-trait continuous-time Markov chain model of phylogeographic diffusion

Partition geography into $K$ discrete sites $\{1, \dots, K\}$ (cities, islands, countries). Let $\tau$ be a rooted, time-measured phylogeny of $N$ taxa with observed tip locations $Y = (y_1, \dots, y_N)$ and unobserved internal and root locations. Along every branch of $\tau$, location evolves as an independent continuous-time Markov chain with infinitesimal generator $\Lambda \in \mathbb{R}^{K \times K}$: off-diagonal entries $\Lambda_{ab} \ge 0$ for $a \ne b$ and rows summing to zero, $\Lambda_{aa} = -\sum_{b \ne a} \Lambda_{ab}$. Finite-time transition probabilities solve the Chapman-Kolmogorov equation and are given by the matrix exponential

$$P(t) \;=\; e^{t\Lambda}, \qquad P_{ab}(t) = \mathbb{P}(\text{at } b \text{ after time } t \mid \text{at } a).$$

To keep the eigendecomposition real, $\Lambda$ is restricted to the time-reversible form

$$\Lambda_{ab} \;=\; \mu\, s_{ab}\, \pi_b \quad (a \ne b), \qquad s_{ab} = s_{ba} > 0, \qquad \pi_a > 0, \ \sum_a \pi_a = 1,$$

with overall rate scalar $\mu$; this is the general time-reversible parameterization, with $K(K-1)/2$ free symmetric rates together with $\pi$, and it satisfies detailed balance $\pi_a \Lambda_{ab} = \pi_b \Lambda_{ba}$, so $\pi$ is the stationary distribution of the chain. $s$ is normalized so that $\sum_a \pi_a \sum_{b \ne a} s_{ab}\pi_b = 1$, i.e. $-\sum_a \pi_a \Lambda_{aa} = \mu$: the overall rate $\mu$ is the expected number of location changes per unit time.

Equivalently the chain is a continuous-time random walk on a graph $\mathcal{G}$ whose vertices are the sites and whose edges carry the rates: from $a$ the walk waits an exponential time with rate $-\Lambda_{aa}$ and then jumps to $b \ne a$ with probability $\Lambda_{ab}/(-\Lambda_{aa})$. For the stationary distribution to be reached from any start, $\mathcal{G}$ must be connected.

Given aligned sequence data $D$ with its own substitution process generator $\Lambda^{\mathrm{seq}}$, and assuming the sequence and location chains are conditionally independent given the tree, the joint posterior factorizes as

$$p(\tau, \Lambda, \Lambda^{\mathrm{seq}}, \theta \mid D, Y) \;\propto\; p(D \mid \tau, \Lambda^{\mathrm{seq}})\; p(Y \mid \tau, \Lambda)\; p(\tau \mid \theta)\; p(\Lambda)\, p(\Lambda^{\mathrm{seq}})\, p(\theta),$$

where $\theta$ holds the clock and coalescent parameters, and both likelihood factors are computed by Felsenstein's pruning algorithm, which integrates over all root and internal states.

## Depends on

- [Site likelihood of a phylogenetic tree](../../felsenstein-s-pruning-algorithm/likelihood.md)
- [Time-reversibility of the GTR chain](../../time-reversible-nucleotide-substitution-models/is-detailed-balance-ctmc-transition-gtr.md)

## Remarks

The model imports the machinery of nucleotide substitution wholesale, with sites replaced by locations, and the import is exactly what creates the statistical difficulty. A sequence alignment offers thousands of sites informing the same rate matrix; a phylogeographic analysis offers one location per taxon, so the $K(K-1)/2$ symmetric rates are fitted to what is effectively a single character. The resulting variance affects not only the rate estimates but the ancestral reconstructions that depend on them, which is the motivation for a sparsity prior over the rates.

Two structural restrictions deserve naming. Reversibility is a modelling convenience, bought for real eigendecompositions, and it is a genuine constraint on geography: a reversible chain cannot encode a source-sink asymmetry in which lineages leave a site faster than they enter it, beyond what the stationary weights $\pi$ express. Discretization is the other: sites are fixed in advance, and locations between or outside them have no representation, so the inferred process depends on the partition chosen.

Joint estimation rather than sequential estimation is what gives the uncertainty its proper width. Reconstructing a tree first and then mapping locations onto the fixed tree discards the uncertainty in topology, branch lengths and clock, and reports ancestral locations more confidently than the data support.

## Sources

- P. Lemey, A. Rambaut, A. J. Drummond, M. A. Suchard, "Bayesian phylogeography finds its roots", PLoS Computational Biology 5(9) (2009) e1000520, Methods, Equations (1)-(3) and (8), <https://doi.org/10.1371/journal.pcbi.1000520> (PMC2740835).
