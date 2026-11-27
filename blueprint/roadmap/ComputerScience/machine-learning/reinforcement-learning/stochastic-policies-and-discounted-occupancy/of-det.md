# Deterministic policy as a stochastic policy

The deterministic policy $\pi : S \to A$ viewed as the stochastic policy that, in each state $s$, takes action $\pi(s)$ with probability $1$: the weight of action $a$ in state $s$ is $1$ if $a = \pi(s)$ and $0$ otherwise. Equivalently, it is the row-stochastic matrix with these weights.
