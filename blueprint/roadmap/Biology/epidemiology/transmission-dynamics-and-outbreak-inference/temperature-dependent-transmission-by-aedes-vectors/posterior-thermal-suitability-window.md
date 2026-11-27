# Posterior thermal suitability window

Let the thermal responses of the traits entering $R_0(T)$ be fitted in a Bayesian framework, inducing a posterior distribution over the function $T \mapsto R_0(T)$. For a probability level $\alpha \in (0,1)$, define the suitability set

$$\mathcal{T}_\alpha = \big\{ T : \Pr\big(R_0(T) > 0 \mid \text{data}\big) \ge \alpha \big\},$$

the set of temperatures at which the posterior probability of non-zero transmission potential reaches $\alpha$. The sets are nested: $\mathcal{T}_{\alpha'} \subseteq \mathcal{T}_\alpha$ for $\alpha \le \alpha'$. When the posterior probability curve $T \mapsto \Pr(R_0(T) > 0 \mid \text{data})$ is unimodal, every $\mathcal{T}_\alpha$ is an interval $[T_{\min}(\alpha), T_{\max}(\alpha)]$; for the source's fitted posterior the reported suitability sets are such intervals. This does not follow from unimodality of each posterior draw: if two equally weighted draws are each positive on one interval and the two intervals are disjoint, $\mathcal{T}_{1/2}$ is their union, which is not an interval. A location is counted as suitable in a given month when its mean temperature for that month lies in $\mathcal{T}_\alpha$, and its exposure is the number of suitable months per year, an integer in $\{0,1,\dots,12\}$.

## Depends on

- [Temperature-dependent reproduction number for a mosquito-borne virus](temperature-dependent-reproduction-number.md)

## Remarks

The cutoff turns a continuous posterior into a binary map, and the choice of $\alpha$ fixes which error is controlled: a high level such as $\alpha = 0.975$ admits a temperature only when transmission is almost certainly not excluded, so areas are called suitable conservatively and the risk of over-stating geographic spread is minimized at the cost of missing marginal areas. Thresholding the posterior probability rather than the posterior mean of $R_0$ keeps parameter uncertainty in the answer: a temperature where $R_0$ is small but confidently positive can qualify, while one where the point estimate is larger but the posterior straddles zero need not. Counting months of suitability rather than averaging $R_0$ over the year preserves seasonality, which matters because a short warm season can support transmission that an annual mean hides, and because warming can push the hottest months above $T_{\max}$ while adding suitable months at the shoulders.

## Sources

- Ryan SJ, Carlson CJ, Mordecai EA, Johnson LR. Global expansion and redistribution of Aedes-borne virus transmission risk with climate change. *PLOS Neglected Tropical Diseases* 13:e0007213 (2019), "The temperature dependent $R_0$ model". DOI <https://doi.org/10.1371/journal.pntd.0007213>. PMCID PMC6438455.
