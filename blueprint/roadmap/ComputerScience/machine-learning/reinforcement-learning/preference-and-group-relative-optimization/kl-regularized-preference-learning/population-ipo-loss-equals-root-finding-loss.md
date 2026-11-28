# The population IPO loss matches the root-finding loss

For complementary preference probabilities, the population IPO loss, built from Bernoulli preference samples, equals the IPO root-finding loss up to an additive constant independent of the policy, which justifies minimizing a loss computed from sampled preferences.

Fix a context and suppress it from the notation. Let $Y$ be finite, $\tau > 0$, $\mu$ a behavior policy, and $p^*(y \succ y') \in [0,1]$ complementary preference probabilities, $p^*(y' \succ y) = 1 - p^*(y \succ y')$ for all $y, y'$ (so $p^*(y \succ y) = 1/2$). Let $\pi_{\mathrm{ref}}$ be a reference policy positive on the support of $\mu$. Let $y, y'$ be independent draws from $\mu$ and, given them, let $I(y,y') \in \{0,1\}$ have mean $p^*(y \succ y')$. Then for every policy $\pi$ positive on the support of $\mu$, with $h_\pi$ and $L$ as in the [IPO loss](identity-preference-optimization-loss.md),

$$\mathbb{E}\Bigl[\bigl(h_\pi(y, y') - \tau^{-1} I(y, y')\bigr)^2\Bigr] = L(\pi) + c,$$

where the constant $c$ does not depend on $\pi$.

## Depends on

- [Identity preference optimization loss](identity-preference-optimization-loss.md)

## Proof depends on

None.

## Expansion

The terms $h_\pi(y,y')^2$ agree and the terms without $h_\pi$ do not depend on $\pi$, so it suffices to compare the cross terms $\mathbb{E}[h_\pi(y,y') I(y,y')]$ and $\mathbb{E}[h_\pi(y,y')(p_y - p_{y'})]$ with $p_y = p^*(y \succ \mu)$. The conditional expectations of the two targets given $(y, y')$ differ, so the equality is not termwise; it uses that $h_\pi(y,y') = a(y) - a(y')$ with $a(y) = \log \pi(y) - \log \pi_{\mathrm{ref}}(y)$, the independence of $y$ and $y'$, $\mathbb{E}_{y' \sim \mu} I(y,y') = p_y$, and, by complementarity, $\mathbb{E}_{y \sim \mu} I(y, y') = 1 - p_{y'}$ and $\mathbb{E}_{y \sim \mu} p_y = 1/2$. Both cross terms then equal $\mathbb{E}_{y \sim \mu}[(2p_y - 1)\, a(y)]$.

The complementarity of preferences is implicit in the source, where $I(y,y')$ is $1$ exactly when $y$ is preferred to $y'$. The lemma licenses replacing the unknown $p^*$ in the root-finding loss by recorded preferences, which leads to the sampled IPO loss.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Proposition 3 and its proof (Section 5.2), equations (13) and (16). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
