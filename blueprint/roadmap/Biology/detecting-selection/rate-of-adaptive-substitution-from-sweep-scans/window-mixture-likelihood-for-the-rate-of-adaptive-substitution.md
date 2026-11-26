# Window-mixture likelihood for the rate of adaptive substitution

Partition a genome into $W$ non-overlapping windows of equal length and summarise window $w$ by $M_w=(w_1,\dots,w_K)\in\{0,1\}^K$, where $w_i=1$ if a likelihood-ratio test of the fitted demographic null model against a hitchhiking model with the $i$-th assigned selection coefficient rejects at a fixed level. Assume windows are independent, recent adaptive substitutions occur at a rate $\delta$ that is homogeneous over windows, and their selection coefficients $s>0$ have density $f(s)$. Then the likelihood of $(\delta,f)$ is

$$L(\delta,f)=\prod_{w=1}^W P(M_w\mid\delta,f),\qquad P(M_w\mid\delta,f)=(1-\delta)\,Q(M_w\mid\text{neutral})+\delta\int_0^\infty f(s)\,Q(M_w\mid s)\,ds,$$

where $Q(M_w\mid\text{neutral})$ and $Q(M_w\mid s)$ are the probabilities of the test outcome vector under the demographic null and under a sweep of strength $s$ (at a random position in the window and a uniformly distributed time within the detectable window), estimated by simulation and rejection sampling. Binning selection coefficients into intervals $[s_j,s_{j+1})$ with $\delta_{s_j,s_{j+1}}=\delta\int_{s_j}^{s_{j+1}}f(s)\,ds$ turns the problem into maximising $L$ over the nonnegative bin rates, with $\delta=\sum_j\delta_{s_j,s_{j+1}}$; no parametric form for $f$ is assumed.

## Remarks

Counting significant windows overestimates sweeps (false positives under a misspecified null) and underestimates them (low power for weak or old sweeps); the mixture likelihood instead uses the full pattern of rejections across a ladder of assigned selection coefficients, which carries information about the true $s$, and corrects for power and false positives through $Q$. Using the fitted demographic history, rather than the standard neutral model, as the null is what keeps demography-induced spectrum distortions from being read as selection. For a derived population, the window outcome is further mixed over sweeps before and after the population split.

## Sources

- H. Li, W. Stephan, "Inferring the demographic history and rate of adaptive substitution in Drosophila", PLoS Genet. 2 (2006) e166, sections "Inferring Selection: General Approach", "Rate of Adaptive Substitution and the Distribution of Selection Coefficients" and "Estimating δ and f(s) for the African population", <https://doi.org/10.1371/journal.pgen.0020166>, PMCID PMC1599771.
