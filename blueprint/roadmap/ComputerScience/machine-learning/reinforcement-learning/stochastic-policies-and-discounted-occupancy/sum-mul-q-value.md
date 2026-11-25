# Sum mul q Value

The policy average of action values is the chain's one-step value:
`∑ a, π s a * qValue M γ V s a = policyReward M π s + γ * ∑ s', stateKernel M π s s' * V s'`.
