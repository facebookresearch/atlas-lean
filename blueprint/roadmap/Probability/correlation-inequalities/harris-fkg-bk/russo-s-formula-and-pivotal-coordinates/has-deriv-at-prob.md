# Derivative of the event weight before grouping

Let $E$ be a finite set and $A \subseteq \{0,1\}^E$. For every $p \in \mathbb{R}$ the [event weight](prob.md) $p \mapsto P_p(A)$ is differentiable at $p$ with derivative

$$\frac{d}{dp} P_p(A) = \sum_{\omega \in A} \sum_{e \in E} W_p^{(e)}(\omega)\, s_e(\omega),$$

where $s_e(\omega) = 1$ if $\omega(e) = 1$ and $s_e(\omega) = -1$ if $\omega(e) = 0$.
