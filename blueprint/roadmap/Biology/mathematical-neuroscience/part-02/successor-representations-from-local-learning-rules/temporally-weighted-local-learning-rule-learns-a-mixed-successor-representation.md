# Temporally weighted local learning rule learns a mixed successor representation

For a Markov chain $S_t$ with transition matrix $P$ and a feature map $\phi: \mathcal S \to \mathbb{R}^m$, the **successor features** are $\mathrm{SF}_\phi(s) = \mathbb{E}\left[\sum_{k\ge0}\gamma^k\phi(S_{t+k}) \mid S_t = s\right]$, $\gamma \in [0,1)$; for indicator features $\phi(s) = e_s$ the **successor representation** is the matrix $\sum_k \gamma^k P^k = (I - \gamma P)^{-1}$ (Eqs. 2–5).

Consider a rate network $\dot p_1 = -p_1 + \sigma(\gamma_1 W_r p_1 + (1-\gamma_1)\phi_1)$ (recurrent, CA3-like) feeding $\dot p_2 = -p_2 + \sigma(\gamma_2 W_f p_1 + (1-\gamma_2)\phi_2)$ (feedforward, CA1-like), whose weights follow the local rule

$$\Delta W = \alpha\left(p^{\mathrm{post}}_{t+1} - W p^{\mathrm{pre}}_t\right)(p^{\mathrm{pre}}_t)^\top + \beta\left(p^{\mathrm{post}}_t - W p^{\mathrm{pre}}_{t+1}\right)(p^{\mathrm{pre}}_{t+1})^\top,$$

a Hebbian term with subtractive normalization (Eqs. 6–11). For $\alpha = \beta$ the rule is invariant under reversal of time; $\alpha = 1, \beta = 0$ is the purely forward rule.

**Claim.** Following the source's analysis, take $\sigma$ to be the identity and the activities at the equilibria of the rate dynamics, $p_1 = (1-\gamma_1)(I - \gamma_1 W_r)^{-1}\phi_1$ and $p_2 = \gamma_2 W_f p_1 + (1-\gamma_2)\phi_2$ (Eqs. 8–9), with weights evolving slowly relative to activities. Let the inputs be $\phi_i(S_t) = \Phi_i e_{S_t}$ for a stationary Markov chain $S_t$ on a finite state space with transition matrix $P$ and positive stationary distribution, with invertible feature matrices $\Phi_i$. Then the averaged weight dynamics has a unique equilibrium, at which the activities encode successor representations under the mixed chain

$$P_{\alpha,\beta} = \frac{\alpha}{\alpha+\beta}P^{\mathrm{forward}} + \frac{\beta}{\alpha+\beta}P^{\mathrm{backward}},$$

so that $p^i_t = \mathrm{SR}^{P_{\alpha_i,\beta_i}}_{\phi_i}(\phi^i_t)$ for each layer $i$ (Keck et al. 2025, Eqs. 19–21 and Appendix D of their S1 Appendices, which normalizes the activities as $p = (I-\gamma W)^{-1}\phi$ and $q = \gamma V p + \psi$, without the factors $1-\gamma_i$). If the recurrent rule is time-symmetric, $\alpha = \beta > 0$, this equilibrium is asymptotically stable (Appendix D, Proposition 1), so the weight updates converge to it under the standard stochastic-approximation conditions (step sizes $\varepsilon_t$ with $\sum_t\varepsilon_t = \infty$, $\sum_t\varepsilon_t^2 < \infty$, and bounded iterates); for other $\alpha, \beta$ the source gives no stability guarantee. At this equilibrium the forward rule $\alpha = 1, \beta = 0$ yields the true successor representation and the time-symmetric rule the successor representation of the reversible symmetrized chain. For the forward rule the layers satisfy $p_1 = (1-\gamma_1)\mathrm{SR}_{\phi_1}$ and $p_2 = (1-\gamma_2)\mathrm{SR}_{\phi_2}$ (Eqs. 17–18).

## Depends on

- [Time-reversal symmetrization of a Markov chain](time-reversal-symmetrization-of-a-markov-chain.md)

## Expansion

At a fixed point of the forward term, $\mathbb{E}[(p_{t+1} - Wp_t)p_t^\top] = 0$, so $W$ is the least-squares one-step predictor of the next activity from the current one, a conditional expectation under $P$. The backward term instead predicts the previous activity from the next, a conditional expectation under the reversed chain, and mixing the two gives prediction under $P_{\alpha,\beta}$. With recurrent gain $\gamma_1$ the fixed point of the activity dynamics sums these one-step predictions geometrically, which yields $(I - \gamma_1 P_{\alpha,\beta})^{-1}$ applied to the input. Biologically, a symmetric rule in CA3 predicts little backward shift of place-field centres on a linear track, while the asymmetric CA1 rule predicts a backward shift.

## Sources

- J. Keck, C. Barry, C. F. Doeller and J. Jost, *Impact of symmetry in local learning rules on predictive neural representations and generalization in spatial navigation*, PLoS Computational Biology (2025), e1013056, Sections 2.2–2.4, Eqs. (2)–(21), and S1 Appendices, Appendix D (Theorem 1, Proposition 1 and Section D.1.1). <https://doi.org/10.1371/journal.pcbi.1013056> (PMCID: PMC12184951)
