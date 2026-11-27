# Average direct, indirect and overall effects under interference

Let units $i = 1, \dots, n$ have potential outcomes $Y_i(w) \in \mathbb{R}$ for treatment vectors $w \in \{0, 1\}^n$, with observed outcomes $Y_i = Y_i(W)$ for a random assignment $W$. Write $Y_j(w_i = x; W_{-i})$ for the outcome of $j$ when unit $i$'s treatment is set to $x$ and the others follow the design. Define

$$\tau_{\mathrm{ADE}} = \frac{1}{n} \sum_{i=1}^{n} \mathbb{E}\bigl\{Y_i(w_i = 1; W_{-i}) - Y_i(w_i = 0; W_{-i})\bigr\},$$

$$\tau_{\mathrm{AIE}} = \frac{1}{n} \sum_{i=1}^{n} \sum_{j \ne i} \mathbb{E}\bigl\{Y_j(w_i = 1; W_{-i}) - Y_j(w_i = 0; W_{-i})\bigr\},$$

and $\tau_{\mathrm{AOE}} = \tau_{\mathrm{ADE}} + \tau_{\mathrm{AIE}}$. In a Bernoulli design, where $W_i \sim \mathrm{Bernoulli}(\pi_i)$ independently with $\pi \in (0, 1)^n$ deterministic, the infinitesimal policy effect is

$$\tau_{\mathrm{INF}}(\pi) = \sum_{k=1}^{n} \frac{\partial}{\partial \pi_k} \mathbb{E}_\pi\Bigl(\frac{1}{n} \sum_{i=1}^{n} Y_i\Bigr).$$

**Theorem.** In a Bernoulli design, $\tau_{\mathrm{AOE}}(\pi) = \tau_{\mathrm{INF}}(\pi)$, conditionally on any realization of the potential outcomes. Without interference, $\tau_{\mathrm{AIE}} = 0$ and $\tau_{\mathrm{ADE}}$ is the usual average treatment effect.

## Expansion

Conditioning on $W_k$, $\mathbb{E}_\pi(Y_i) = \pi_k \mathbb{E}_\pi\{Y_i(w_k = 1; W_{-k})\} + (1 - \pi_k)\mathbb{E}_\pi\{Y_i(w_k = 0; W_{-k})\}$, where the inner expectations do not involve $\pi_k$ because the treatments are independent. So $\partial \mathbb{E}_\pi(Y_i) / \partial \pi_k$ is the marginalized effect of unit $k$'s treatment on unit $i$; summing over $k$ and averaging over $i$ gives $\tau_{\mathrm{ADE}} + \tau_{\mathrm{AIE}}$. The indirect effect is thus the part of the effect of nudging all treatment probabilities that is not captured by the direct effect.

## Sources

- Y. Hu, S. Li and S. Wager, *Average direct and indirect causal effects under interference*, Biometrika (2022). <https://doi.org/10.1093/biomet/asac008> Assumption 1, Definitions 1–4 and Theorem 1, with the proof of Theorem 1 in the appendix.
