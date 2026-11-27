# Pareto–Beta finite mixture model of the VAF spectrum

**Setting.** Let $X = \{x_1, \dots, x_n\}$ be variant allele frequencies of somatic mutations in copy-number-neutral regions of one tumour sample, assumed i.i.d. Under neutral within-clone growth (a birth–death branching process, or the Luria–Delbrück limit), the number of mutations at frequency $f$ decays as $1/f^2$ over the detectable range; positively selected clones contribute unimodal clusters on $[0,1]$.

**Model.** For $k \ge 1$ Beta components and one Pareto Type-I component, the likelihood is

$$p(X \mid \theta, \pi) = \prod_{i=1}^{n} \Big[ \pi_1\, g(x_i \mid x_*, \alpha) + \sum_{w=2}^{k+1} \pi_w\, h(x_i \mid a_{w-1}, b_{w-1}) \Big],$$

with mixing weights $\pi$ on the $(k+1)$-simplex, Pareto density $g(x \mid x_*, \alpha) = \alpha x_*^{\alpha} x^{-(\alpha+1)}$ for $x \ge x_*$ (zero otherwise; scale $x_* > 0$, shape $\alpha > 0$), and Beta density $h(x \mid a, b) = x^{a-1}(1-x)^{b-1}/B(a,b)$ on $[0,1]$. Setting $\pi_1 = 0$ gives the tail-free model.

**Estimation (EM / iterated moments).** With responsibilities $z_{i,j} \propto \pi_j \cdot (\text{component } j \text{ density at } x_i)$, normalized over $j$:

1. The Pareto scale is fixed at the cutoff $x_* = \min X$, the smallest observed frequency, before the iterations. For the endpoint-inclusive density above, this is the maximum likelihood estimate of the scale for a sample drawn from the Pareto component alone; in the mixture it is a fixed choice of the procedure, not a claim that it maximizes the likelihood jointly with the other parameters.
2. Given $x_*$, the weighted MLE of the Pareto shape is

    $$\hat\alpha = \frac{\sum_i z_{i,1}}{\sum_i z_{i,1} \log(x_i / x_*)} .$$

3. Each Beta component is updated by weighted moment matching: $\hat\mu_j = \sum_i z_{i,j} x_i / (n\pi_j)$, $\hat\sigma_j^2 = \sum_i z_{i,j}(x_i - \hat\mu_j)^2/(n\pi_j)$, and, using mean $a/(a+b)$ and variance $ab/((a+b)^2(a+b+1))$,

    $$\hat a_j = \hat\mu_j\, c_j, \quad \hat b_j = (1 - \hat\mu_j)\, c_j, \qquad c_j = \frac{\hat\mu_j(1-\hat\mu_j)}{\hat\sigma_j^2} - 1,$$

    valid when $\hat\sigma_j^2 < \hat\mu_j(1-\hat\mu_j)$.

**Model selection.** With negative log-likelihood $\mathrm{NLL}$ and $|\Theta| = 3k+2$ free parameters with a tail ($3k-1$ without), $\mathrm{BIC} = 2\,\mathrm{NLL} + |\Theta| \log n$. The integrated classification likelihood adds the assignment entropy, $\mathrm{ICL} = \mathrm{BIC} + H(z)$, with $H(z) = -\sum_{j}\sum_i z_{i,j}\log z_{i,j}$. The reduced-entropy criterion $\mathrm{reICL} = \mathrm{BIC} + H(\hat z)$ computes the entropy only over mutations whose hard assignment is not the tail, renormalized over the Beta components. Fits with and without a tail, for $1 \le k \le K$, compete under the chosen score.

## Expansion

The Pareto tail with $\alpha \approx 1$ is the continuous analogue of the $1/f^2$ density of the neutral spectrum, whose cumulative form is the classical $M(f) \propto 1/f$ law. Because all clones share the same mutation rate, the tails emitted by every clone have the same exponent and can be pooled into a single Pareto component, decoupling tail and clusters into an ordinary finite mixture. The likelihood of a pure Pareto sample, $\alpha^n x_*^{n\alpha}\prod_i x_i^{-(\alpha+1)}$ for $x_* \le \min X$ and $0$ otherwise, increases in $x_*$, which gives the scale estimate; with the endpoint excluded the likelihood would vanish at $x_* = \min X$ and have no maximizer. Moment matching replaces the Beta M-step, which has no closed form, at the cost of losing the monotone-likelihood guarantee of EM. The Pareto component overlaps all subclonal clusters by construction, so full ICL penalizes tails heavily; reICL drops that part of the penalty and only demands separation among Beta components. Mutations assigned to the tail are polyphyletic and are removed before clustering read counts into selected subclones.

## Sources

- G. Caravagna, T. Heide, M. J. Williams, et al., "Subclonal reconstruction of tumors by using machine learning and population genetics", Nature Genetics 52 (2020) 898–907, Online Methods ("Model-based clustering of cancer subclonal populations with MOBSTER", "Distributions and likelihood", "Fitting MOBSTER", "Clustering assignments and model selection"), <https://doi.org/10.1038/s41588-020-0675-5> (PMC7610388).
