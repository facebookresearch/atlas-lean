# Conductance of a set for a Markov kernel

For real weights $K : \alpha \times \alpha \to \mathbb{R}$ and $\pi : \alpha \to \mathbb{R}$ on a finite set $\alpha$, the conductance of a set $S$ is $\Phi(S) = \sum_{x \in S} \sum_{y \notin S} \pi(x) K(x, y) \big/ \sum_{x \in S} \pi(x)$, which is $0$ when $\sum_{x \in S} \pi(x) = 0$ by the convention for division by zero. When $K$ is a Markov kernel and $\pi$ a stationary law, it is the stationary flow out of $S$ divided by the stationary mass of $S$.
