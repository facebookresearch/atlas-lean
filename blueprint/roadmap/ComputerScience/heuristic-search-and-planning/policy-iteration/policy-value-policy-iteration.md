# Policy iteration terminates

Let $M$ be a Markov decision process with a finite set of
states $S$, a finite nonempty set of actions $A$, real rewards and stochastic transition
probabilities, and let $0 \le \gamma < 1$. Write $V^\pi$ for the value of a deterministic policy
$\pi : S \to A$, $V^*$ for the optimal value, and $N = |A|^{|S|}$ for the number of deterministic
policies. For every deterministic policy $\pi$, the policy $\pi_N$ obtained after $N$ steps of
policy iteration from $\pi$ is optimal: $V^{\pi_N} = V^*$.
