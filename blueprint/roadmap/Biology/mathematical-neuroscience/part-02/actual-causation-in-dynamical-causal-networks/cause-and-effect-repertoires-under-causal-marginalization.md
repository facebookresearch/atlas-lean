# Cause and effect repertoires under causal marginalization

**Dynamical causal network.** Fix background conditions $U = u$ and finite-state variables in two consecutive time slices $V = \{V_{t-1}, V_t\}$, with all parents of $V_t$ in $V_{t-1}$ and no within-slice edges. Assume the causal Markov condition and causal sufficiency, so the transition probabilities factorise and are interventional:

$$p_u(v_t\mid v_{t-1}) = \prod_i p\big(v_{i,t}\mid \mathrm{do}(v_{t-1}), u\big).$$

A *transition* $v_{t-1}\prec v_t$ is a realisation with $p_u(v_t\mid v_{t-1}) > 0$; an *occurrence* is a sub-state $x_{t-1}\subseteq v_{t-1}$ or $y_t \subseteq v_t$.

**Effect repertoire.** For an occurrence $x_{t-1}$ over $X_{t-1}$, let $W = V_{t-1}\setminus X_{t-1}$ with state space $\Omega_W$. For a single node,

$$\pi(Y_{i,t}\mid x_{t-1}) = \frac{1}{|\Omega_W|}\sum_{w\in\Omega_W} p_u\big(Y_{i,t}\mid \mathrm{do}(x_{t-1}, W = w)\big),$$

i.e. variables outside the occurrence are replaced by a uniform average over their states (*causal marginalization*). For several nodes, $\pi(Y_t\mid x_{t-1}) = \prod_i \pi(Y_{i,t}\mid x_{t-1})$, which discards correlations among the $Y_{i,t}$ induced by common inputs in $W$.

**Cause repertoire.** For a single node, by Bayes' rule with a uniform prior,

$$\pi(X_{t-1}\mid y_{i,t}) = \frac{\sum_{w\in\Omega_W} p_u\big(y_{i,t}\mid \mathrm{do}(X_{t-1}, W = w)\big)}{\sum_{z\in\Omega_{V_{t-1}}} p_u\big(y_{i,t}\mid \mathrm{do}(V_{t-1} = z)\big)},$$

and for a multivariate occurrence the normalised product

$$\pi(X_{t-1}\mid y_t) = \frac{\prod_i \pi(X_{t-1}\mid y_{i,t})}{\sum_{x\in\Omega_{X_{t-1}}}\prod_i \pi(X_{t-1} = x\mid y_{i,t})}.$$

**Unconstrained repertoires** (conditioning on the empty occurrence, $\pi(\varnothing) = 1$):

$$\pi(X_{t-1}) = |\Omega_{X_{t-1}}|^{-1},\qquad \pi(Y_t) = \prod_i |\Omega_{V_{t-1}}|^{-1}\sum_{w} p_u\big(Y_{i,t}\mid \mathrm{do}(V_{t-1} = w)\big).$$

**Cause and effect information.** For a candidate effect $y_t$ of $x_{t-1}$, or candidate cause $x_{t-1}$ of $y_t$,

$$\rho_e(x_{t-1}, y_t) = \log_2\frac{\pi(y_t\mid x_{t-1})}{\pi(y_t)},\qquad \rho_c(x_{t-1}, y_t) = \log_2\frac{\pi(x_{t-1}\mid y_t)}{\pi(x_{t-1})}.$$

They are pointwise-mutual-information-like quantities but need not be equal, because the repertoires are product distributions; $\rho = 0$ when conditioning on the empty set, and $\rho > 0$ is necessary (not sufficient) for an actual effect or cause.

## Expansion

The uniform average in causal marginalization makes the repertoire a property of the mechanism rather than of the observed distribution of other variables: every counterfactual state of the background inputs is tested with equal weight. Example: with an OR gate and an AND gate both reading $(\mathrm{OR},\mathrm{AND})_{t-1}$, the occurrence $\{\mathrm{OR}_{t-1} = 1\}$ raises the probability of $\{\mathrm{OR}_t = 1\}$ from $3/4$ to $1$, giving $\rho_e = \log_2(4/3) \approx 0.415$ bits.

## Sources

- L. Albantakis, W. Marshall, E. Hoel, G. Tononi, *What Caused What? A Quantitative Account of Actual Causation Using Dynamical Causal Networks*, Entropy 21 (2019), 459, Sections 2.1–2.4 (Eqs. 1–6, 11, 12). <https://doi.org/10.3390/e21050459> (PMCID: PMC7514949)
