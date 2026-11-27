# The gamma-centroid estimator

**Setting.** Many bioinformatics predictions are binary vectors $y \in \mathcal{Y} \subseteq \{0, 1\}^n$: a
pairwise alignment (which position pairs are aligned), an RNA secondary structure (which base pairs
form), a tree topology (which splits are present). Given data $D$ and a posterior distribution
$p(\theta \mid D)$ on $\mathcal{Y}$ (from a pair HMM, a stochastic context-free grammar, an energy model,
or MCMC samples), a **maximum expected gain (MEG) estimator** maximizes
$\mathbb{E}_{\theta \mid D}[G(\theta, y)]$ over $y \in \mathcal{Y}$. The maximum likelihood estimator is
the MEG estimator for the delta gain $G(\theta, y) = [\theta = y]$, and the **centroid estimator** is the
MEG estimator for the number of correctly predicted coordinates, equivalently the minimizer of
expected Hamming loss. Write $p_i = P(\theta_i = 1 \mid D)$ for the marginal probabilities (alignment or
base-pairing probabilities).

**Definition.** For $\gamma > 0$, the **$\gamma$-centroid estimator** is the MEG estimator for the gain

$$G_\gamma(\theta, y) = \gamma \cdot \mathrm{TP}(\theta, y) + \mathrm{TN}(\theta, y) = \sum_{i=1}^{n} \bigl(\gamma [\theta_i = 1][y_i = 1] + [\theta_i = 0][y_i = 0]\bigr);$$

$\gamma = 1$ is the centroid estimator.

**Theorem.**

1. For constants $\alpha_1, \dots, \alpha_4 > 0$, the MEG estimator for
   $\alpha_1 \mathrm{TP} + \alpha_2 \mathrm{TN} - \alpha_3 \mathrm{FP} - \alpha_4 \mathrm{FN}$ is the
   $\gamma$-centroid estimator with $\gamma = \frac{\alpha_1 + \alpha_4}{\alpha_2 + \alpha_3}$.
2. $\mathbb{E}[G_\gamma(\theta, y) \mid D] = \sum_{i} \bigl((\gamma + 1) p_i - 1\bigr) y_i + \mathrm{const}$.
   Hence, if $\mathcal{Y}$ is closed under switching any coordinate from 1 to 0, the $\gamma$-centroid
   estimator maximizes the sum of the marginal probabilities $p_i > \frac{1}{\gamma + 1}$ included in
   the prediction.
3. If moreover $\mathcal{Y}$ is defined by "at most one 1 in each of a family of index sets" (as for
   alignments and pseudoknot-free or general base pairings) and $0 < \gamma \le 1$, the estimator is the
   consensus estimator $\hat{y}_i = [p_i > \frac{1}{\gamma + 1}]$, which is then guaranteed to lie in
   $\mathcal{Y}$.

## Expansion

The expected gain is linear in $y$ with coefficient $(\gamma + 1)p_i - 1$ on coordinate $i$, because the
TN term contributes $1 - p_i$ when $y_i = 0$ and the TP term $\gamma p_i$ when $y_i = 1$. Coordinates with
negative coefficient are never worth predicting, and deleting positives keeps a prediction feasible,
so the optimization reduces to a weighted problem over the coordinates above the threshold, solved by
Needleman-Wunsch-type or Nussinov-type dynamic programming on the marginal probability matrix. When
$\gamma \le 1$ the threshold is at least $1/2$, and two coordinates in the same exclusion set cannot both
have probability above $1/2$, so thresholding alone already gives a feasible prediction. Because
sensitivity, positive predictive value, MCC and F-score are functions of TP, TN, FP and FN, tuning
$\gamma$ trades sensitivity against PPV within a single principled family, unlike ad hoc
maximum-expected-accuracy scores that weight these counts with a bias.

## Sources

- M. Hamada, H. Kiryu, W. Iwasaki, K. Asai, "Generalized centroid estimators in bioinformatics",
  PLoS ONE 6 (2011) e16450, Definitions 3-7, Theorems 1-3 and Corollary 1,
  <https://doi.org/10.1371/journal.pone.0016450> (PMC3041832).
