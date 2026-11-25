# Uniqueness of the solution of a policy's Bellman equation

Let $M$ be a Markov decision
process with finitely many states, real rewards and stochastic transition probabilities, let
$0 \le \gamma < 1$, and let $\pi$ be a deterministic stationary policy, a map from states to
actions. If a real-valued function $V$ on the states satisfies $T_\pi V = V$, where $T_\pi$ is the
Bellman operator of $\pi$ in $M$ with discount $\gamma$, then $V$ is the value of $\pi$.
