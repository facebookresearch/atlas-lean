# Sampling-based corticostriatal bandit learning

A corticostriatal circuit can implement exploration by sampling: each action is represented by an ensemble of synapses whose weights form a population code for the action's value, sparse premotor activity samples a random subset of that ensemble, a winner-take-all motor stage picks the action with the largest sample, and dopaminergic reward prediction errors update the chosen ensemble. With suitable sparsity, learning rates and initial weights this algorithm has near-minimax regret on multi-armed bandits.

- [Regret bound for sparse-sampling corticostriatal learning](regret-bound-for-sparse-sampling-corticostriatal-learning.md)
