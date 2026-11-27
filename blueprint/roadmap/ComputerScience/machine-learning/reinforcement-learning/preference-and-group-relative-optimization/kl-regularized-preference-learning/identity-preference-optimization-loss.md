# Identity preference optimization loss

Identity preference optimization (IPO) learns a policy from preference data by regressing the gap $h_\pi(y_w, y_l)$ between the policy's and the reference's log-likelihood ratios onto the constant $1/(2\tau)$. Its population form is a squared regression loss built from preference probabilities.

Fix a context and suppress it from the notation, as in the source. Let $Y$ be finite, $\pi_{\mathrm{ref}}$ a reference policy, $\mu$ a behavior policy, $\tau > 0$, and $p^*(y \succ y')$ preference probabilities with $p^*(y \succ \mu) = \mathbb{E}_{y' \sim \mu} p^*(y \succ y')$. For a policy $\pi$ positive on the responses involved put

$$h_\pi(y, y') = \log \frac{\pi(y)\, \pi_{\mathrm{ref}}(y')}{\pi(y')\, \pi_{\mathrm{ref}}(y)}.$$

The **IPO root-finding loss** is

$$L(\pi) = \mathbb{E}_{y, y' \sim \mu}\Bigl[\Bigl(h_\pi(y, y') - \frac{p^*(y \succ \mu) - p^*(y' \succ \mu)}{\tau}\Bigr)^2\Bigr],$$

the **population IPO loss** is $\mathbb{E}_{y, y' \sim \mu}\bigl[(h_\pi(y,y') - \tau^{-1} I(y,y'))^2\bigr]$, where $I(y,y') \in \{0,1\}$ is a Bernoulli preference sample with mean $p^*(y \succ y')$, and for a finite dataset $\mathcal{D}$ of pairs $(y_w, y_l)$ with $y_w$ preferred the **sampled IPO loss** is

$$\mathbb{E}_{(y_w, y_l) \sim \mathcal{D}}\Bigl[\Bigl(h_\pi(y_w, y_l) - \frac{1}{2\tau}\Bigr)^2\Bigr],$$

the average over $\mathcal{D}$. With contexts, $h_\pi$ uses $\pi(\cdot \mid x)$ and $\pi_{\mathrm{ref}}(\cdot \mid x)$, and the dataset consists of triples $(x, y_w, y_l)$.

## Depends on

- [Ψ-preference optimization](psi-preference-optimization.md)

## Proof depends on

None.

## Expansion

The maximizer of the [IPO objective](psi-preference-optimization.md) is $\pi^*(y) \propto \pi_{\mathrm{ref}}(y) \exp(\tau^{-1} p^*(y \succ \mu))$, so $h_{\pi^*}(y, y') = \tau^{-1}(p^*(y \succ \mu) - p^*(y' \succ \mu))$ on the support of $\pi_{\mathrm{ref}}$ and $L(\pi^*) = 0$; $L$ turns these root-finding equations into one optimization problem. Its minimizer is unique under a support condition ([uniqueness of the IPO minimizer](uniqueness-of-the-ipo-minimizer.md)), and $L$ differs from the population IPO loss by a constant ([lemma](sampled-ipo-loss-equals-root-finding-loss.md)). Each datapoint $(y_w, y_l)$ contributes the two samples $(y_w, y_l, 1)$ and $(y_l, y_w, 0)$ to an empirical population loss, $\tfrac12\bigl[(h_\pi(y_w,y_l) - \tau^{-1})^2 + h_\pi(y_w,y_l)^2\bigr]$, which equals the sampled IPO loss up to an additive constant.

Unlike the logistic DPO loss, the squared loss keeps the log-ratio gap bounded when the data record only wins for an action. In the source's two-action example with $p^*(y_1 \succ y_2) = 1$ and uniform $\pi_{\mathrm{ref}} = \mu$, the IPO optimum is $\pi^*(y_1) = \sigma(1/(2\tau))$, which tends to the reference policy as $\tau \to \infty$, whereas a Bradley–Terry fit would need an infinite reward gap and DPO's limiting policy is deterministic for every $\tau$.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 5.1, equations (9) to (13), Section 5.2, equations (16) and (17) and Algorithm 1, and Section 5.3.1 (two-action example), with Section 4.2. [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
