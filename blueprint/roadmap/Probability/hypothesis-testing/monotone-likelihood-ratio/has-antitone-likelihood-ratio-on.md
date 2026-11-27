# Antitone likelihood ratio

Let $L : \mathbb{N} \times \mathbb{R} \to \mathbb{R}$ be a likelihood family and $S \subseteq \mathbb{R}$. The family has an *antitone likelihood ratio* on $S$ if $L(n, \theta) \ge 0$ for all $n$ and $\theta \in S$, and for $n \le m$ and $\theta \le \theta'$ in $S$,

$$L(n, \theta)\, L(m, \theta') \le L(m, \theta)\, L(n, \theta').$$

For positive likelihoods this says that $\theta \mapsto L(m, \theta)/L(n, \theta)$ is nonincreasing (larger counts favour smaller parameters).
