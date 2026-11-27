# Riesz representer and the doubly robust moment of a linear functional

Let $W$ be a random vector with law $\mathrm{pr}$, $Y \in \mathbb R$ an outcome with $\mathbb E(Y^2) < \infty$, $L_2 = L_2(\mathrm{pr})$, and $\Gamma \subseteq L_2$ a linear subspace. Let $m(W,\gamma)$ define the target $\theta_0 = \mathbb E\{m(W,\gamma_0)\}$, with $\gamma_0 \in \Gamma$ (e.g. $\gamma_0(w) = \mathbb E(Y\mid W=w)$).

**Assumption (linearity and mean-square continuity).** $\gamma \mapsto \mathbb E\{m(W,\gamma)\}$ is linear and there are $\bar Q < \infty$, $q > 0$ with $\mathbb E\{m(W,\gamma)^2\} \le \bar Q\,[\mathbb E\{\gamma(W)^2\}]^q$ for all $\gamma \in \Gamma$.

**Lemma ([Riesz representation](../../../../../Analysis/hilbert-spaces/riesz-representation-hilbert.md)).** Under the assumption there is $\alpha_0 \in L_2$ with $\mathbb E\{m(W,\gamma)\} = \mathbb E\{\alpha_0(W)\gamma(W)\}$ for all $\gamma \in \Gamma$. There is a unique *minimal* Riesz representer $\alpha_0^{\min} \in \overline{\Gamma}$, the projection of any $\alpha_0$ onto $\overline\Gamma$, and $[\mathbb E\{\alpha_0^{\min}(W)^2\}]^{1/2} = \bar M \le \bar Q^{1/2}$, where $\bar M$ is the operator norm of $\gamma \mapsto \mathbb E\{m(W,\gamma)\}$.

**Doubly robust moment.** If $\gamma_0$ is the regression (or the projection of $\mathbb E(Y\mid W)$ onto $\Gamma$), then for all $\gamma, \alpha \in \Gamma$

$$\theta_0 = \mathbb E\big[m(W,\gamma_0) + \alpha(W)\{Y-\gamma_0(W)\}\big] = \mathbb E\big[m(W,\gamma) + \alpha_0^{\min}(W)\{Y - \gamma(W)\}\big],$$

so the moment is correct if either nuisance is correct. All expectations here exist: $m(W,\gamma) \in L_2$ by mean-square continuity, and $\alpha$, $\alpha_0^{\min}$, $\gamma$, $\gamma_0$ and $Y$ are square integrable. These are population identities; consistency of estimators built from fitted nuisances is a separate matter (see the [finite-sample Gaussian approximation](debiased-machine-learning-finite-sample-gaussian-approximation.md)).

Example: for the average treatment effect with $W = (D,X)$, $D \in \{0,1\}$, $m(W,\gamma) = \gamma(1,X)-\gamma(0,X)$ and propensity $\pi_0(x) = \mathrm{pr}(D = 1 \mid X = x)$, assume overlap, $0 < \pi_0(X) < 1$ almost surely, and $\mathbb E[1/\{\pi_0(X)(1 - \pi_0(X))\}] < \infty$ (for instance $\pi_0$ bounded away from $0$ and $1$). Then the representer $\alpha_0(d,x) = d/\pi_0(x) - (1-d)/(1-\pi_0(x))$ lies in $L_2$, giving the augmented inverse-probability-weighted moment; without such integrability the functional need not be mean-square continuous and the representer need not be square integrable.

## Proof depends on

- [Riesz representation theorem for Hilbert spaces](../../../../../Analysis/hilbert-spaces/riesz-representation-hilbert.md)

## Expansion

The first equality holds because $\mathbb E[\alpha(W)\{Y-\gamma_0(W)\}] = 0$ for $\alpha \in \Gamma$ by the projection property of $\gamma_0$. For the second, $\mathbb E[m(W,\gamma)] - \mathbb E[m(W,\gamma_0)] = \mathbb E[\alpha_0^{\min}(\gamma - \gamma_0)]$ by linearity and Riesz representation, which cancels against $\mathbb E[\alpha_0^{\min}\{\gamma_0 - \gamma\}]$. Mean-square continuity gives boundedness of the functional, hence existence of the representer.

## Sources

- Victor Chernozhukov, Whitney K. Newey and Rahul Singh, "A simple and general debiased machine learning theorem with finite-sample guarantees", Biometrika 110 (2023), 257–264, <https://doi.org/10.1093/biomet/asac033>; author manuscript <https://par.nsf.gov/servlets/purl/10471116>. Numbering of the published journal edition: Section 3, Assumption 1, Lemma 1 and the doubly robust estimating equation that follows it (arXiv:2105.15197 numbers them differently).
