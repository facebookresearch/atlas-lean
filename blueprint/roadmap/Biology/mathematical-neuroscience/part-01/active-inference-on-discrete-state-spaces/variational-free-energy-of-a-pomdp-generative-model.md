# Variational free energy of a POMDP generative model

**Generative model.** Fix finite sets of hidden states and outcomes, a horizon $T$, a current time $t \le T$ and a finite set $\Pi$ of policies (action sequences). The joint distribution over observations $o_{1:t}$, hidden states $s_{1:T}$, the likelihood matrix $A$ and the policy $\pi$ factorizes as

$$P(o_{1:t}, s_{1:T}, A, \pi) = P(A)\,P(\pi)\,P(s_1)\prod_{\tau=2}^{T}P(s_\tau \mid s_{\tau-1},\pi)\prod_{\tau=1}^{t}P(o_\tau \mid s_\tau, A),$$

with categorical transitions and likelihood $P(o_\tau \mid s_\tau, A)$ given by the columns of $A$, and a Dirichlet prior $P(A)$.

**Mean-field posterior.** Take approximate posteriors of the form

$$Q(s_{1:T}, A, \pi) = Q(A)\,Q(\pi)\prod_{\tau=1}^{T}Q(s_\tau \mid \pi).$$

**Decomposition.** The variational free energy $F[Q] = \mathbb{E}_{Q}\big[\log Q(s_{1:T},A,\pi) - \log P(o_{1:t}, s_{1:T}, A, \pi)\big]$ equals

$$F[Q] = D_{KL}[Q(A)\,\|\,P(A)] + D_{KL}[Q(\pi)\,\|\,P(\pi)] + \mathbb{E}_{Q(\pi)}\big[F_\pi[Q(s_{1:T}\mid\pi)]\big],$$

where the policy-conditioned free energy is

$$F_\pi = \sum_{\tau=1}^{T}\mathbb{E}_{Q(s_\tau\mid\pi)}[\log Q(s_\tau\mid\pi)] - \sum_{\tau=1}^{t}\mathbb{E}_{Q(s_\tau\mid\pi)Q(A)}[\log P(o_\tau\mid s_\tau,A)] - \mathbb{E}_{Q(s_1\mid\pi)}[\log P(s_1)] - \sum_{\tau=2}^{T}\mathbb{E}_{Q(s_\tau\mid\pi)Q(s_{\tau-1}\mid\pi)}[\log P(s_\tau\mid s_{\tau-1},\pi)].$$

Since $F[Q] = D_{KL}[Q \,\|\, P(\cdot \mid o_{1:t})] - \log P(o_{1:t})$, minimizing $F$ over the mean-field family is approximate Bayesian inference, and $F$ upper-bounds the surprisal $-\log P(o_{1:t})$.

## Depends on

- [Evidence lower bound of a single observation](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mean-field-variational-inference/elbo.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)
- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Expansion

Both factorizations turn the logarithms into sums; grouping the $A$-terms gives $D_{KL}[Q(A)\|P(A)]$ plus the expected log-likelihood, the $\pi$-terms give $D_{KL}[Q(\pi)\|P(\pi)]$, and the remaining terms, which depend on $\pi$, are averaged under $Q(\pi)$. Setting the gradient of $F_\pi$ with respect to the categorical parameters of $Q(s_\tau\mid\pi)$ to zero gives softmax fixed-point updates that combine forward and backward messages with the expected log-likelihood $\mathbb{E}_{Q(A)}[\log A] = \psi(a) - \psi(a_0)$ (digamma of the Dirichlet counts); a gradient descent on $F_\pi$ is read as neuronal dynamics, and the same updates coincide with variational message passing.

## Sources

- L. Da Costa, T. Parr, N. Sajid, S. Veselic, V. Neacsu, K. Friston, "Active inference on discrete state-spaces: a synthesis", Journal of Mathematical Psychology 99 (2020) 102447, Sections 4.2–4.3, Eqs. (5)–(6), <https://doi.org/10.1016/j.jmp.2020.102447>, PMCID PMC7732703.
