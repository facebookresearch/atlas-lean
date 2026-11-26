# Mutation-additive multinomial logistic model of lineage growth

Cluster pathogen genomes into lineages $c = 1, \dots, C$, and let $X \in \{0,1\}^{C \times K}$ record which of $K$ amino-acid substitutions each lineage carries. For region $r$ and time $t$, let $y_{r,t} \in \mathbb N^C$ be the counts of sequenced genomes per lineage, with total $n_{r,t}$. The model is

$$y_{r,t} \sim \mathrm{Multinomial}\bigl(n_{r,t},\ p_{r,t}\bigr), \qquad
p_{r,t,c} = \frac{\exp(a_{r,c} + b_{r,c}\,t)}{\sum_{c'}\exp(a_{r,c'} + b_{r,c'}\,t)},$$

with region-specific intercepts $a_{r,c}$ (introduction times and initial prevalence) and region-specific growth rates $b_{r,c}$ shrunk hierarchically toward a lineage-level growth rate

$$b_c = \sum_{k=1}^{K} X_{c,k}\,\beta_k ,$$

where $\beta_k$ is the additive effect of mutation $k$ on the exponential growth rate, under a regularizing prior. The relative fitness of lineage $c$ against $c'$ is the growth-rate difference $b_c - b_{c'}$. For any two lineages in one region the log prevalence ratio is linear in time,

$$\log\frac{p_{r,t,c}}{p_{r,t,c'}} = (a_{r,c} - a_{r,c'}) + (b_{r,c} - b_{r,c'})\,t ,$$

so the model reduces pairwise to logistic replacement. A lineage with mutation content $x$ that has not yet been observed gets the predicted growth rate $\sum_k x_k\hat\beta_k$. Inference over millions of genomes uses stochastic variational inference.

## Expansion

If each lineage's incidence grows exponentially as $e^{a + b t}$ with a lineage-specific rate, then lineage shares are the normalized exponentials above whatever the shared epidemic trend, because the trend cancels in the ratio. Sampled genomes are then multinomial draws from those shares. Tying growth rates to mutations means a substitution that arises independently in several lineages is estimated from all of them (convergent evolution adds power), and lineage-level estimates stabilize sooner than with lineage counts alone. The additive form omits epistasis between mutations. Applied to 6.4 million SARS-CoV-2 genomes with 3,000 clusters and 2,904 substitutions, leave-one-lineage-out predictions from mutation content alone tracked the fitted lineage growth rates.

## Sources

- F. Obermeyer, M. Jankowiak, N. Barkas, S. F. Schaffner, et al., "Analysis of 6.4 million SARS-CoV-2 genomes identifies mutations associated with fitness", Science 376 (2022), main text (model description and fig. S1) and Supplementary Materials (model specification), <https://doi.org/10.1126/science.abm1208> (PMC9161372).
