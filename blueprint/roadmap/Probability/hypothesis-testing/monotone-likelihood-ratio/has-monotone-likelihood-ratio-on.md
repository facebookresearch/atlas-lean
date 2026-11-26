# Monotone likelihood ratio

Let $L : \mathbb{N} \times \mathbb{R} \to \mathbb{R}$, $(n, \theta) \mapsto L(n, \theta)$, be a likelihood family (observation $n$, parameter $\theta$) and $S \subseteq \mathbb{R}$ a parameter set. The family has a *monotone likelihood ratio* on $S$ if $L(n, \theta) \ge 0$ for all $n$ and $\theta \in S$, and for observations $n \le m$ and parameters $\theta \le \theta'$ in $S$,

$$L(m, \theta)\, L(n, \theta') \le L(n, \theta)\, L(m, \theta')$$

(total positivity of order two). For positive likelihoods this is monotonicity of $\theta \mapsto L(m, \theta)/L(n, \theta)$. The nonnegativity is part of the definition: without it the [posterior tail](posterior-tail.md) would not be a posterior probability (a signed $L$ can give a value larger than $1$).
