# Aspiration-independent sigma rule for aspiration dynamics on regular networks

In the aspiration dynamics of a two-strategy $d$-player game on a regular network of degree $d - 1$ (payoffs $a_k$, $b_k$; personal aspirations $e_i$; decision functions $g_i(\beta(e_i - \pi_i))$), assume each $g_i$ is differentiable with $g_i' > 0$ and $0 < g_i < 1$ on $\mathbb{R}$.

**Theorem.** In the limit of weak selection $\beta \to 0^+$ there are $d$ coefficients $\sigma_0, \dots, \sigma_{d-1}$, depending on the decision functions, the population size and the network but on neither the payoff entries nor the aspirations, such that strategy $A$ is more abundant than $B$ (average abundance above $\tfrac12$) whenever

$$\sum_{k=0}^{d-1} \sigma_k \,\big(a_k - b_{d-1-k}\big) > 0.$$

In particular, heterogeneous personal aspirations select the same strategy as a homogeneous aspiration level.

## Depends on

- [Aspiration dynamics: equal abundance under vanishing selection or neutral payoffs](abundance-one-half-under-neutral-payoffs.md)

## Expansion

Because the $g_i$ are differentiable, the stationary abundance of $A$ is $\tfrac12 + \beta\, D + o(\beta)$, and $D$ is a linear form $\sum_k \alpha_k a_k + \sum_k \omega_k b_k + \sum_i \phi_i e_i$ with no constant term (Lemma 1 of the source). Applying the neutral-payoff case with all payoffs zero forces $\sum_i \phi_i e_i = 0$ for every aspiration vector, so every $\phi_i = 0$. Swapping the labels $A$ and $B$ and using that the two abundances sum to one gives $\alpha_k = -\omega_{d-1-k}$, and setting $\sigma_k = \alpha_k$ yields the stated rule. As with the classical sigma rule, $\sigma_k$ can be read off from the single payoff table with $a_k = 1$ and all other entries $0$.

## Sources

- B. Wu, L. Zhou, *Individualised aspiration dynamics: Calculation by proofs*, PLoS Comput. Biol. 14(9) (2018), e1006035 (Lemma 1, Lemma 2, Theorem 1, Eqs. (1)–(9)). <https://doi.org/10.1371/journal.pcbi.1006035> (PMCID: PMC6177198)
