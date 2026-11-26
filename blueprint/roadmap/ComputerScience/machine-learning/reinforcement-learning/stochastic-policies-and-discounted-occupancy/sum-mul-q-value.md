# Sum mul q Value

For any matrix of action weights $\pi : S \to A \to \mathbb R$, any $V : S \to \mathbb R$ and any state $s$, the $\pi$-weighted sum of action values is the one-step value of the induced chain:
`∑ a, π s a * qValue M γ V s a = policyReward M π s + γ * ∑ s', stateKernel M π s s' * V s'`.
The identity is algebraic: the weights $\pi(s, a)$ need not be nonnegative or sum to $1$. For a stochastic policy $\pi$ the left side is the policy average of the action values.
