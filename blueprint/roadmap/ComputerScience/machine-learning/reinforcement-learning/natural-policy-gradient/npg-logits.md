# Natural policy gradient iterates

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For a step size $\eta$, natural policy gradient with softmax policies starts from $\theta_0 = 0$ and updates

$$\theta_{t+1} = \theta_t + \frac{\eta}{1-\gamma} A^{\pi_{\theta_t}},$$

equivalently $\pi_{t+1}(a \mid s) \propto \pi_t(a \mid s) \exp\bigl(\eta A^{\pi_t}(s,a)/(1-\gamma)\bigr)$: multiplicative weights in every state, with the advantages as gains, as in the [Hedge algorithm](../../online-learning-and-boosting/hedge-algorithm/README.md). This is the closed form that the Fisher-preconditioned update $\theta \leftarrow \theta + \eta F(\theta)^\dagger \nabla V^{\pi_\theta}$ takes for softmax policies on the states reachable from the start distribution $\rho$ (AKLM, Lemma 5.1 and footnote 6), up to a state-dependent offset that the softmax ignores (AJKS Lemma 12.6). Here the soft policy iteration is applied at every state; the iteration is defined by its closed form, without the derivation from the Fisher update.

## Sources

- S. Kakade, *A Natural Policy Gradient*, NeurIPS 2001
- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Lemma 5.1
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 12.6
