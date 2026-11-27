# Expected free energy as risk plus ambiguity

Use the generative model of [Variational free energy of a POMDP generative model](variational-free-energy-of-a-pomdp-generative-model.md). Fix a future time $\tau > t$, let $P(s_\tau, A)$ be the preferred (target) distribution over final states and parameters specified by the generative model, and let $Q = Q(o_\tau, s_\tau, A, \pi) \approx P(o_\tau, s_\tau, A, \pi \mid o_{1:t})$ be the predictive approximate posterior, in which policies and outcomes are conditionally independent given $(s_\tau, A)$.

**Expected free energy.** The posterior over policies is

$$Q(\pi) = \sigma(-G(\pi)), \qquad G(\pi) = \underbrace{D_{KL}[Q(s_\tau,A\mid\pi)\,\|\,P(s_\tau,A)]}_{\text{risk}} \;\underbrace{-\;\mathbb{E}_{Q(s_\tau,A\mid\pi)P(o_\tau\mid s_\tau,A)}[\log P(o_\tau\mid s_\tau,A)]}_{\text{ambiguity}},$$

where $\sigma$ is the softmax over $\Pi$; the ambiguity term is the expected entropy of outcomes given states, $\mathbb{E}_{Q(s_\tau,A\mid\pi)}H[P(o_\tau\mid s_\tau,A)]$.

**Lemma 1 (steady state).** Suppose $D_{KL}[Q(s_\tau,A)\,\|\,P(s_\tau,A)] < \infty$. For $\beta \ge 0$ let

$$G(\pi;\beta) = D_{KL}[Q(s_\tau,A\mid\pi)\,\|\,P(s_\tau,A)] - \mathbb{E}_{Q(o_\tau,s_\tau,A\mid\pi)}[\beta\log P(o_\tau\mid s_\tau,A)],$$

with $\beta = \mathbb{E}_Q[\log Q(\pi\mid s_\tau,A)] \,/\, \mathbb{E}_Q[\log P(o_\tau\mid s_\tau,A)]$. Then the predicted distribution reaches the target, $Q(s_\tau,A) = P(s_\tau,A)$, if and only if

$$\mathbb{E}_Q[-\log Q(\pi)] = \mathbb{E}_Q[G(\pi;\beta)].$$

**Corollary 2.** Under the same finiteness assumption, each softmax posterior $Q(\pi) = \sigma(-G(\pi;\beta))$ with $\beta \ge 0$ describes a system that reaches a steady-state distribution; $\beta = 1$ gives the expected free energy $G(\pi)$ above, and $\beta = 0$ gives KL (risk-sensitive) control, $G(\pi;0) = D_{KL}[Q(s_\tau,A\mid\pi)\|P(s_\tau,A)]$.

## Depends on

- [Variational free energy of a POMDP generative model](variational-free-energy-of-a-pomdp-generative-model.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Expansion

The proof of Lemma 1 writes $\mathbb{E}_Q[G(\pi;\beta)]$ using $Q(s_\tau,A\mid\pi)Q(\pi) = Q(\pi\mid s_\tau,A)Q(s_\tau,A)$; the choice of $\beta$ exactly cancels the policy-entropy term against the outcome log-likelihood, leaving $\mathbb{E}_Q[G(\pi;\beta)] = \mathbb{E}_Q[-\log Q(\pi)] + D_{KL}[Q(s_\tau,A)\,\|\,P(s_\tau,A)]$. The identity in the lemma therefore holds iff the divergence vanishes; when the divergence is infinite, $Q$ is not absolutely continuous with respect to the target. Policies that minimize risk drive predicted states toward preferences (exploitation), and policies that minimize ambiguity seek states with informative outcomes (exploration); the most likely action is then the Bayesian model average $u_t = \arg\max_u \sum_{\pi:\pi_t = u}Q(\pi)$.

## Sources

- L. Da Costa, T. Parr, N. Sajid, S. Veselic, V. Neacsu, K. Friston, "Active inference on discrete state-spaces: a synthesis", Journal of Mathematical Psychology 99 (2020) 102447, Section 6.1, Eqs. (10)–(11), Appendix C (Lemma 1, Corollary 2, Eqs. (C.1)–(C.3)), <https://doi.org/10.1016/j.jmp.2020.102447>, PMCID PMC7732703.
