# A priori error bound for value iteration

Let $M$ be a Markov decision process with
finitely many states, a nonempty finite set of actions, real rewards and stochastic transition
probabilities, let $0 \le \gamma < 1$, and let $T$ be the Bellman optimality operator and $V^*$
the optimal value of $M$ with discount $\gamma$. For every real-valued function $V$ on the states
and every $n \in \mathbb{N}$, the result $T^n V$ of $n$ steps of value iteration from $V$ satisfies
$\|T^n V - V^*\|_\infty \le \|V - TV\|_\infty \, \gamma^n / (1 - \gamma)$, where
$\|\cdot\|_\infty$ is the sup norm.
