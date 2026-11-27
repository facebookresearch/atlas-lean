# Bayes factor test for an individual diffusion rate

In the [stochastic search variable selection model](stochastic-search-variable-selection-over-migration-graphs.md) for phylogeographic diffusion among $K$ sites, let $\delta_{ab}$ be the indicator of the edge $\{a,b\}$ and let $E = K(K-1)/2$. Write

$$\hat{p}_{ab} \;=\; \mathbb{P}\bigl(\delta_{ab} = 1 \,\bigm|\, D, Y\bigr) \;=\; \mathbb{E}\bigl[\delta_{ab} \mid D, Y\bigr]$$

for the posterior inclusion probability of the edge, estimated by the Monte Carlo average of the indicator, and let $p_{ab} = \mathbb{P}(\delta_{ab} = 1)$ be its prior inclusion probability. The Bayes factor for the rate contributing to the migration graph is the ratio of posterior to prior odds,

$$\mathrm{BF}_{ab} \;=\; \frac{\hat{p}_{ab} \,/\, (1 - \hat{p}_{ab})}{p_{ab} \,/\, (1 - p_{ab})} .$$

Under the truncated Poisson prior on the number of edges, whose mean is set so that the minimal connected configuration of $K-1$ edges carries prior probability $1/2$, symmetry across edges gives

$$p_{ab} \;=\; \frac{\mathbb{E}\bigl[\sum_{a<b} \delta_{ab}\bigr]}{E},$$

the same value for every pair. Rates with $\mathrm{BF}_{ab} \ge 3$ are reported as well-supported, and the edges they index constitute the inferred migration graph.

## Depends on

- [Stochastic search variable selection over migration graphs](stochastic-search-variable-selection-over-migration-graphs.md)

## Remarks

The quantity is a Bayes factor in the strict sense: for the two nested models $\delta_{ab} = 1$ and $\delta_{ab} = 0$, with all other parameters integrated out, the ratio of marginal likelihoods equals the ratio of posterior odds to prior odds, which is what the displayed formula computes without ever evaluating a marginal likelihood. Dividing by the prior odds is what makes the summary comparable across analyses: because the prior deliberately concentrates on sparse graphs, $p_{ab}$ is small, and a posterior inclusion probability that looks unremarkable in absolute terms can still represent a large update.

Two consequences follow from the structure. First, the test is a statement about a route, not about a count of migration events: an edge can be well supported while the posterior number of transitions along it is small, and an edge with many parsimony-inferred events can fail the test if those events are explained by other routes. Second, $p_{ab}$ depends on $K$ through $E$, so adding sites to the discretization lowers the prior odds of every individual edge and mechanically raises the Bayes factors of the edges that survive; comparisons of Bayes factors across analyses with different site partitions are therefore not like for like.

Reporting only the thresholded edges also hides the uncertainty that the model was built to express. Complementary summaries used with it are the Kullback-Leibler divergence of the posterior root-location distribution from its prior, $D(\hat{\pi}_{\mathrm{root}} \| \pi_{\mathrm{root}})$, which measures how much the data say about the origin and is zero when posterior equals prior, and an association index comparing the observed clustering of tip locations on the tree with its distribution under random permutation of those locations, with low values indicating spatial structure and values near one indicating admixture.

## Sources

- P. Lemey, A. Rambaut, A. J. Drummond, M. A. Suchard, "Bayesian phylogeography finds its roots", PLoS Computational Biology 5(9) (2009) e1000520, Methods, "Bayes factor test of significant diffusion rates" (Equations (6) and (7)), "Summarizing posterior location uncertainty" (Equation (9)) and "Association index" (Equation (10)), <https://doi.org/10.1371/journal.pcbi.1000520> (PMC2740835).
