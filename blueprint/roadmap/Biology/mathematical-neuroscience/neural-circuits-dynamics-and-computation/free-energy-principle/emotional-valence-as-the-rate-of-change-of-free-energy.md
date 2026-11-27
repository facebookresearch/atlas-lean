# Emotional valence as the rate of change of free energy

**Variational free energy.** An agent with generative model $m$ receives sensory data $y$ caused by hidden states $\vartheta$, and holds a recognition density $q(\vartheta \mid \mu)$ with sufficient statistics $\mu$. With positive finite evidence $p(y \mid m)$ and $F(y, \mu)$ the [variational free energy](variational-free-energy-bound-on-surprise.md) of $q$, the Kullback–Leibler divergence from $q$ to the true posterior decomposes as

$$D_{\mathrm{KL}}\big[q(\vartheta \mid \mu)\,\|\,p(\vartheta \mid y, m)\big] = F(y, \mu) + \ln p(y \mid m) \qquad \text{(Eq. 1)},$$

so that

$$F(y, \mu) = D_{\mathrm{KL}}\big[q(\vartheta \mid \mu)\,\|\,p(\vartheta \mid y, m)\big] - \ln p(y \mid m) \;\ge\; -\ln p(y \mid m) \qquad \text{(Eq. 2)},$$

and, equivalently, complexity minus accuracy,

$$F = D_{\mathrm{KL}}\big[q(\vartheta \mid \mu)\,\|\,p(\vartheta \mid m)\big] - \mathbb{E}_q\big[\ln p(y \mid \vartheta, m)\big] \qquad \text{(Eq. 3)}.$$

Free energy is an upper bound on surprise $-\ln p(y \mid m)$; minimizing it over $\mu$ makes $q$ an approximate posterior, and minimizing it through action changes $y$.

**Definition (valence).** At level $i$ of a hierarchical model with free energy $F_i(t)$, emotional valence is the negative rate of change of free energy,

$$\mathrm{valence}_i(t) = -\frac{dF_i}{dt}.$$

**Basic forms of emotion.** Using the sign of $\dot F_i$ and of $\ddot F_i$:

| $\dot F_i$ | $\ddot F_i$ | emotion | valence |
|---|---|---|---|
| $< 0$ | $> 0$ | happiness | positive (factive) |
| $> 0$ | $< 0$ | unhappiness | negative (factive) |
| $< 0$ | $< 0$ | hope | positive (epistemic) |
| $> 0$ | $> 0$ | fear | negative (epistemic) |
| $= 0$ | $= 0$ | surprise (low or high) | neutral |
| changes sign $+ \to -$ | | relief | positive |
| changes sign $- \to +$ | | disappointment | negative |

**Proposition (transitions).** Along any twice-differentiable free-energy trajectory, a passage from a negative emotion to a positive one must pass through relief, and from a positive to a negative one through disappointment, while transitions within the negative (fear, unhappiness) or the positive (hope, happiness) emotions are possible in both directions.

## Depends on

- [Variational free energy as an upper bound on surprise](variational-free-energy-bound-on-surprise.md)

## Expansion

Rearranging Eq. 1 gives Eq. 2, and since the divergence is nonnegative $F$ bounds surprise from above; expanding $p(\vartheta \mid y, m) = p(y \mid \vartheta, m)p(\vartheta \mid m)/p(y \mid m)$ in the divergence gives Eq. 3. Valence is positive when the agent's model of the world is improving (free energy falling) and negative when it is deteriorating. The transition rule follows from continuity of $\dot F_i$: valence changes sign only where $\dot F_i$ crosses zero, and those crossings are exactly relief and disappointment. The source couples valence back to inference by letting it regulate posterior uncertainty, so that falling valence raises the learning rate in volatile environments, a meta-learning scheme that performs comparably to an agent explicitly tracking volatility.

## Sources

- M. Joffily and G. Coricelli, "Emotional valence and the free-energy principle", PLoS Computational Biology 9(6) (2013) e1003094, Eqs. 1–3, section "Basic forms of emotion" and Table 1, <https://doi.org/10.1371/journal.pcbi.1003094> (PMC3681730).
