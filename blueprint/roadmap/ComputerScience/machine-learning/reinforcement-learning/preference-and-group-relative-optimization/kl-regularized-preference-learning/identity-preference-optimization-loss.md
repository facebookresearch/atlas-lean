# Identity preference optimization loss

Identity preference optimization (IPO) learns a policy from preference data by regressing the gap $h_\pi(y_w, y_l)$ between the policy's and the reference's log-likelihood ratios onto the constant $1/(2\tau)$. Its population form is a squared regression loss built from preference probabilities.

Fix a context and suppress it from the notation, as in the source. Let $Y$ be finite, $\mu$ a behavior policy, $\pi_{\mathrm{ref}}$ a reference policy positive on the support of $\mu$, $\tau > 0$, and $p^*(y \succ y')$ preference probabilities with $p^*(y \succ \mu) = \mathbb{E}_{y' \sim \mu} p^*(y \succ y')$. For a policy $\pi$ positive on the support of $\mu$, and $y,y'$ in that support, put

$$h_\pi(y, y') = \log \frac{\pi(y)\, \pi_{\mathrm{ref}}(y')}{\pi(y')\, \pi_{\mathrm{ref}}(y)}.$$

The **IPO root-finding loss** is

$$L(\pi) = \mathbb{E}_{y, y' \sim \mu}\Bigl[\Bigl(h_\pi(y, y') - \frac{p^*(y \succ \mu) - p^*(y' \succ \mu)}{\tau}\Bigr)^2\Bigr],$$

the **population IPO loss** is $\mathbb{E}_{y, y' \sim \mu}\bigl[(h_\pi(y,y') - \tau^{-1} I(y,y'))^2\bigr]$, where $I(y,y') \in \{0,1\}$ is a Bernoulli preference sample with mean $p^*(y \succ y')$, and for a finite nonempty dataset $\mathcal{D}$ of pairs $(y_w, y_l)$ in the support of $\mu$, with $y_w$ preferred, the **sampled IPO loss** is

$$\mathbb{E}_{(y_w, y_l) \sim \mathcal{D}}\Bigl[\Bigl(h_\pi(y_w, y_l) - \frac{1}{2\tau}\Bigr)^2\Bigr],$$

the average over $\mathcal{D}$. Here $\log$ is the natural logarithm. The edition cited below prints, in its equation (17) and in step 2 of its Algorithm 1, the positive multiple $\tau$ times this loss, $\mathbb{E}_{(y_w, y_l) \sim \mathcal{D}}\bigl[\tau\,(h_\pi(y_w, y_l) - \tau^{-1}/2)^2\bigr]$, while equation (17) of arXiv:2310.12036v1 and v2 has no factor $\tau$; for fixed $\tau$, the rescaling changes neither the minimizers nor the direction of the gradient. With contexts, $h_\pi$ uses $\pi(\cdot \mid x)$ and $\pi_{\mathrm{ref}}(\cdot \mid x)$, and the dataset consists of triples $(x, y_w, y_l)$.

## Depends on

- [Ψ-preference optimization](psi-preference-optimization.md)

## Proof depends on

None.

## Expansion

The maximizer of the [IPO objective](psi-preference-optimization.md) is $\pi^*(y) \propto \pi_{\mathrm{ref}}(y) \exp(\tau^{-1} p^*(y \succ \mu))$, so $h_{\pi^*}(y, y') = \tau^{-1}(p^*(y \succ \mu) - p^*(y' \succ \mu))$ on the support of $\pi_{\mathrm{ref}}$ and $L(\pi^*) = 0$; $L$ turns these root-finding equations into one optimization problem. Its minimizer is unique under a support condition ([uniqueness of the IPO minimizer](uniqueness-of-the-ipo-minimizer.md)), and, for complementary preferences $p^*(y' \succ y) = 1 - p^*(y \succ y')$, $L$ differs from the population IPO loss by a constant ([lemma](population-ipo-loss-equals-root-finding-loss.md)). Each datapoint $(y_w, y_l)$ contributes the two samples $(y_w, y_l, 1)$ and $(y_l, y_w, 0)$ to an empirical population loss; since $h_\pi(y_l, y_w) = -h_\pi(y_w, y_l)$, the symmetrized term is $\tfrac12\bigl[(h_\pi(y_w,y_l) - \tau^{-1})^2 + h_\pi(y_w,y_l)^2\bigr] = \bigl(h_\pi(y_w,y_l) - \tfrac{1}{2\tau}\bigr)^2 + \tfrac{1}{4\tau^2}$. So the symmetrized empirical loss equals the sampled IPO loss above plus $1/(4\tau^2)$, which is $\tau^{-1}$ times the cited edition's printed form plus the same constant.

Unlike the logistic DPO loss, the squared loss keeps the log-ratio gap bounded when the data record only wins for an action. In the source's two-action example with $p^*(y_1 \succ y_2) = 1$ and uniform $\pi_{\mathrm{ref}} = \mu$, the IPO optimum is $\pi^*(y_1) = \sigma(1/(2\tau))$, which tends to the reference policy as $\tau \to \infty$, whereas a Bradley–Terry fit would need an infinite reward gap and DPO's limiting policy is deterministic for every $\tau$.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 5.1, equations (9) to (13), Section 5.2, equations (16) and (17) and Algorithm 1 (printed with the outer factor $\tau$), and Section 5.3.1 (two-action example), with Section 4.2. [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, arXiv:2310.12036v2 (2023), equation (17) and Algorithm 1, printed without the factor $\tau$. [arXiv](https://arxiv.org/abs/2310.12036v2)
