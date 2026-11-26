# Rippler algorithm for non-centred inference in individual-level epidemic models

**Setting.** An individual-level discrete-time epidemic is a coupled hidden Markov model: individuals $j = 1,\dots,N$ have hidden states $x_{t,j} \in \{1,\dots,S\}$ at times $t = 1,\dots,T$ (e.g. S, I, R), partially observed through $y_{t,j} \sim f(\cdot \mid x_{t,j},\theta)$. Transition probabilities $p^{(t,j)}_{r,s} = \mathbb{P}(x_{t+1,j} = s \mid x_{t,j} = r, \mathbf{x}_{t,-j}, \theta)$ depend on everyone's current state; from a rate matrix $Q^{(t,j)}$ they are taken as $p_{r,r} = e^{q_{r,r}}$ and $p_{r,s} = \frac{q_{r,s}}{-q_{r,r}}\big(1 - e^{q_{r,r}}\big)$ for $s \ne r$. In non-centred form, each state is a deterministic function of a uniform variable,

$$x_{t+1,j} = g\big(u_{t+1,j};\, p^{(t,j)}_{x_{t,j},\cdot}\big), \qquad g(u; p_1,\dots,p_S) = 1 + \sum_{s=1}^S \mathbf{1}\Big\{u > \sum_{r \le s} p_r\Big\},$$

so the whole latent history is $\mathbf{X} = G(\mathbf{U},\theta)$ for a matrix $\mathbf{U}$ of uniforms.

**Algorithm.** Given $\theta$ and the current history $\mathbf{X}$:
1. For each $(t,j)$ compute the interval $(u^{low}_{t,j}, u^{upp}_{t,j})$ of uniforms that reproduce $x_{t,j}$ given the previous states, and draw $u_{t,j}$ uniformly from it.
2. Choose a pair $(t,j)$ with probability proportional to $1 - u^{upp}_{t,j} + u^{low}_{t,j}$ and redraw $u^\ast_{t,j}$ uniformly from $(0,u^{low}_{t,j}) \cup (u^{upp}_{t,j},1)$, which forces $x^\ast_{t,j} \ne x_{t,j}$; keep the other uniforms.
3. Regenerate $\mathbf{X}^\ast = G(\mathbf{U}^\ast,\theta)$ forward in time; the change "ripples" through later states of the individual and of everyone it can infect.
4. Accept with probability

$$\alpha(\mathbf{X},\mathbf{X}^\ast) = \min\Big\{1,\ \frac{\pi(\mathbf{Y}\mid\theta,\mathbf{X}^\ast)}{\pi(\mathbf{Y}\mid\theta,\mathbf{X})}\cdot\frac{\sum_{t,j}\big(1 - u^{upp}_{t,j} + u^{low}_{t,j}\big)}{\sum_{t,j}\big(1 - u^{upp,\ast}_{t,j} + u^{low,\ast}_{t,j}\big)}\Big\},$$

alternating with any standard MCMC update of $\theta$ given $\mathbf{X}$ and $\mathbf{Y}$.

**Proposition.** The acceptance ratio reduces to this form because (i) $\pi(\mathbf{X}\mid\theta)\,q_1(\mathbf{U}\mid\theta,\mathbf{X}) = 1$, since the density of $\mathbf{U}$ given $\mathbf{X}$ is the product of $1/(u^{upp}_{t,j} - u^{low}_{t,j})$ and those interval lengths are exactly the transition probabilities that make up $\pi(\mathbf{X}\mid\theta)$, and likewise for $\mathbf{X}^\ast$; and (ii) $\mathbf{X}^\ast$ is a deterministic function of $\mathbf{U}^\ast$, so its conditional proposal probability is one. Only the observation likelihood and the normalising lengths of the "move" regions remain, and the chain targets $\pi(\theta,\mathbf{X}\mid\mathbf{Y})$.

## Expansion

Centred samplers that change one individual's infection time at a time mix poorly, because the proposed history must stay consistent with everyone else's infections. Non-centring moves the randomness into $\mathbf{U}$, whose prior is fixed and independent of $\theta$: a single changed uniform proposes a whole new history that is automatically consistent with the transmission model, which is why the prior terms cancel. Changing several uniforms at once ($\kappa$ elements) gives larger moves; an $\epsilon$-greedy adaptive rule chooses $\kappa$ to keep the acceptance rate near $0.234$. A data-informed variant builds the mapping $g$ from probabilities that also use the observation data, which helps when transitions between any two states are possible, as in multi-strain models. Compared with reversible-jump MCMC and individual forward-filtering backward-sampling (iFFBS), the Rippler algorithms perform better as the number of disease states grows: their cost scales linearly in the number of states, against quadratically for iFFBS.

## Sources

- James Neill, Lloyd A. C. Chapman, Chris Jewell, "Non-centred Bayesian inference for discrete-valued state-transition models: the Rippler algorithm", arXiv:2602.10924 (2026), Section 2 (coupled hidden Markov models, transition probabilities, non-centred simulation), Section 3 (proposal mechanism, Propositions 1–3, acceptance probability, adaptive tuning, Algorithm 1, data-informed Rippler) and Supplementary Material, <https://doi.org/10.48550/arXiv.2602.10924>.
