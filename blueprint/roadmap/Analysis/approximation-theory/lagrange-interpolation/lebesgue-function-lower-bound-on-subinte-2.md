# Tao's lower bound for the Lebesgue function on subintervals

This settles [Erdős Problem 1153 on the Lebesgue function on subintervals](lebesgue-function-lower-bound-on-subinte.md) in the affirmative: its statement holds. For all real $a, b$ with $-1 \le a < b \le 1$ and every $\varepsilon > 0$, for all sufficiently large $n$ and every family of $n$ distinct nodes $x_1, \dots, x_n \in [-1, 1]$, some $t \in [a, b]$ satisfies $\lambda(t) > (2/\pi - \varepsilon) \log n$, where $\lambda(t) = \sum_k |\ell_k(t)|$ is the Lebesgue function of the Lagrange basis polynomials $\ell_k$ of the nodes.

This follows from an estimate of Tao (Theorem 1.10(i)): for a fixed interval $I \subseteq [-1, 1]$ there is a constant $C$ such that, for all large $n$ and all distinct nodes in $[-1, 1]$, $\sup_{x \in I} \lambda(x) \ge (2/\pi) \log n - C$. Take $I = [a, b]$. Once $\varepsilon \log n > C$, the supremum is strictly greater than $(2/\pi - \varepsilon) \log n$, so some $t \in [a, b]$ has $\lambda(t) > (2/\pi - \varepsilon) \log n$; since $\lambda$ is continuous, the supremum over the closed interval is also attained. Bernstein had proved the case $I = [-1, 1]$, and Erdős and Szabados a lower bound of order $\log n$; erdosproblems.com/1153 lists the problem as proved on the strength of Tao's preprint.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1153, https://www.erdosproblems.com/1153 (status PROVED); resolution: T. Tao, Local Bernstein theory, and lower bounds for Lebesgue constants, arXiv:2603.21453 (2026), Theorem 1.10(i): for a fixed interval I ⊆ [-1, 1], all large n and distinct nodes x₁ < ⋯ < xₙ in [-1, 1], sup_{x ∈ I} λ(x) ≥ (2/π) log n - O(1); erdosproblems.com/1153 accepts this as the resolution, https://arxiv.org/abs/2603.21453.
