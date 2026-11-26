# Proliferation-weighted optimal transport loss

For source points $x_1, \dots, x_N$ (cells simulated forward by the [potential-driven diffusion](potential-driven-diffusion-fitted-by-a-wasserstein-loss.md)) and target points $y_1, \dots, y_M$ (cells observed at the next time point), with nonnegative weights $\alpha \in \mathbb{R}^N$, $\beta \in \mathbb{R}^M$ of equal total mass, the transport cost is

$$\min_{\pi} \sum_{i,j} \pi_{ij} C_{ij} \quad \text{subject to} \quad \pi_{ij} \ge 0, \;\; \sum_{j} \pi_{ij} = \alpha_i, \;\; \sum_{i} \pi_{ij} = \beta_j, \qquad C_{ij} = \lVert x_i - y_j \rVert^2 .$$

Proliferation enters through the source weights: $\alpha_i$ is proportional to the expected number of descendants $n_i$ of cell $x_i$ over the interval, while the empirical weights $\beta_j$ are uniform. Under a birth-death process with birth rate $b$ and death rate $d$ over an interval of length $\Delta t$,

$$n = \exp\big(\Delta t\,(b - d)\big), \qquad g = b - d = \frac{\log n}{\Delta t}.$$

With lineage-tracing barcodes, $n_i$ is the number of cells carrying the clone's barcode at the later time divided by the number carrying it at the current time (with a pseudocount of $1$); otherwise $b$ and $d$ are logistic functions of smoothed cell-cycle and apoptosis gene-set scores.

## Depends on

- [Potential-driven diffusion fitted to single-cell time series by a Wasserstein loss](potential-driven-diffusion-fitted-by-a-wasserstein-loss.md)
- [Mean population size of the linear birth–death process](../../../../Probability/branching-processes/linear-birth-death-process/has-sum-mul-prob.md)

## Expansion

With uniform weights the loss only matches shapes of distributions, so a population that expands in one region and shrinks in another is misfit by spurious drift. Upweighting a cell by its expected number of descendants lets it be matched to proportionally many cells at the later time, which is what a balanced transport plan with marginal $\alpha$ enforces; this keeps the problem balanced, in contrast with unbalanced optimal transport, which relaxes the marginal constraints by growth rates. The mean of a linear birth-death process started from one cell is $e^{(b-d)\Delta t}$, which gives the formula for $n$. Including proliferation improved agreement of simulated fate biases with clonal lineage-tracing data in haematopoiesis.

## Sources

- G. H. T. Yeo, S. D. Saksena and D. K. Gifford, "Generative modeling of single-cell time series with PRESCIENT enables prediction of cell trajectories with interventions", Nature Communications 12 (2021), <https://doi.org/10.1038/s41467-021-23518-w> (PMC8163769). Methods, Equations (4)-(9).
