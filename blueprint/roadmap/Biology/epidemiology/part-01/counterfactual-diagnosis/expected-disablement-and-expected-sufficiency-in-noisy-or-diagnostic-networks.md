# Expected disablement and expected sufficiency in noisy-OR diagnostic networks

**Setting.** A three-layer diagnostic Bayesian network has binary risk factors $R$, diseases $D_j$ and
symptoms $S$, read as a structural causal model. Each symptom is a **noisy-OR** of its parents: an
active parent $D$ switches $S$ on unless its activation fails, independently with probability
$\lambda_{D,S}$ (a leak term covers causes outside the model). Given evidence $\mathcal{E}$ with present
symptoms $S_{+}$ and absent symptoms $S_{-}$, counterfactual probabilities
$P(S' \mid \mathcal{E}, \mathrm{do}(X = x))$ describe the symptoms that would have been observed under an
intervention, and are computed with a twin network.

**Definitions.** The **expected disablement** of disease $D$ is the expected number of present symptoms
that would switch off if $D$ were cured,

$$E_{\mathrm{dis}}(D, \mathcal{E}) = \sum_{S'} |S_{+} \setminus S'_{+}|\, P\bigl(S' \mid \mathcal{E}, \mathrm{do}(D = 0)\bigr),$$

and its **expected sufficiency** is the expected number of present symptoms that would persist if all
other direct causes of the present symptoms were switched off,

$$E_{\mathrm{suff}}(D, \mathcal{E}) = \sum_{S'} |S'_{+}|\, P\bigl(S' \mid \mathcal{E}, \mathrm{do}(\mathrm{Pa}(S_{+}) \setminus D = 0)\bigr).$$

**Theorem (desiderata).** Both measures (i) are proportional to the posterior probability of the
disease (consistency), (ii) vanish for a disease that cannot cause any present symptom (causality),
and (iii) favor diseases that explain more of the present symptoms (simplicity). The posterior
$P(D = 1 \mid \mathcal{E})$ satisfies only (i).

**Theorem (closed form).** In three-layer noisy-OR networks both measures of disease $D_k$ equal

$$\sum_{Z \subseteq S_{+}} (-1)^{|Z|}\, \frac{P(S_{-} = 0, Z = 0, D_k = 1 \mid R)}{P(S_{\pm} \mid R)}\, \tau(k, Z),$$

with $\tau(k, Z) = \sum_{S \in S_{+} \setminus Z} (1 - \lambda_{D_k, S})$ for the expected sufficiency and
$\tau(k, Z) = \sum_{S \in Z} \bigl(1 - \frac{1}{\lambda_{D_k, S}}\bigr)$ for the expected disablement.

## Depends on

- [Counterfactual probability given evidence](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/cf-prob.md)

## Expansion

Ranking by posterior asks which disease the patient most likely has; ranking by a counterfactual
asks which disease best explains the symptoms, which is the clinical question when common
comorbidities are probable but explain nothing. In a noisy-OR model the exogenous noise of each
parent-symptom link is a Bernoulli failure, so conditioning the twin network on the factual
evidence and intervening on the disease reduces to inclusion-exclusion over which present symptoms
are turned off, giving the alternating sum; each term needs only ordinary posterior queries of the
factual network. Expected sufficiency assumes diseases are sufficient causes of their symptoms; the
expected disablement is the fallback when that fails.

## Sources

- J. G. Richens, C. M. Lee, S. Johri, "Improving the accuracy of medical diagnosis with causal
  machine learning", Nature Communications 11 (2020), Definitions 1-2, Theorems 1-2 and
  Eqs. 3-7, <https://doi.org/10.1038/s41467-020-17419-7> (PMC7419549).
