# Log-determinant potential of Online Newton Step

Let $\varepsilon > 0$, let $\nabla_1, \dots, \nabla_T \in \mathbb{R}^n$ satisfy $\lVert \nabla_t \rVert \le G$, and let $A_0 = \varepsilon I_n$ and $A_t = A_{t-1} + \nabla_t \nabla_t^{\mathsf T}$. Then

$$\sum_{t=1}^T \nabla_t^{\mathsf T} A_t^{-1} \nabla_t \le \log \frac{\lvert A_T \rvert}{\lvert A_0 \rvert} \le n \log\Big(\frac{T G^2}{\varepsilon} + 1\Big),$$

where $\lvert \cdot \rvert$ is the determinant.

## Proof

For positive definite $A \succeq B \succ 0$, $A^{-1} \bullet (A - B) \le \log(\lvert A \rvert / \lvert B \rvert)$ (Hazan, Lemma 4.7); apply it with $A = A_t$ and $B = A_{t-1}$, for which
$A^{-1} \bullet (A - B) = \nabla_t^{\mathsf T} A_t^{-1} \nabla_t$, and telescope. The largest eigenvalue of $A_T$ is at most $T G^2 + \varepsilon$, so $\lvert A_T \rvert \le (T G^2 + \varepsilon)^n$, while
$\lvert A_0 \rvert = \varepsilon^n$.

## Related topics

- [Online Newton Step for exp-concave losses](online-newton-step-for-exp-concave-losses.md)

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207, Section 4.4 (proof of Theorem 4.5) and Lemma 4.7. <https://arxiv.org/pdf/1909.05207>
