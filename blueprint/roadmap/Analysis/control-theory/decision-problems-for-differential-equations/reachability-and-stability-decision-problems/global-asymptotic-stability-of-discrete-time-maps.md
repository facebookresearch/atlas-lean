# Global asymptotic stability of a discrete-time system

The discrete-time system x⁺ = φ(x) on ℝⁿ, with φ(0) = 0, is globally asymptotically stable when every trajectory converges to the origin and trajectories that start near the origin stay near it.

**Definition.** Let $\varphi : \mathbb R^n \to \mathbb R^n$ with $\varphi(0) = 0$, and consider the autonomous discrete-time system $x_{k+1} = \varphi(x_k)$. It is *globally asymptotically stable* (the origin is a globally asymptotically stable equilibrium) if

1. (global attractivity) for every initial state $x_0 \in \mathbb R^n$, $\lim_{k \to \infty} x_k = 0$; and
2. (Lyapunov stability) for every $\varepsilon > 0$ there is $\delta > 0$ such that $\|x_0\|_2 \le \delta$ implies $\|x_k\|_2 \le \varepsilon$ for all $k \ge 0$.

For a closed-loop system $x_{k+1} = f(x_k, \psi(x_k))$ obtained from a plant $x^+ = f(x, u)$ and a feedback law $u = \psi(x)$, the definition applies to $\varphi(x) = f(x, \psi(x))$.

## Depends on

- [Discrete-time dynamical system](../../discrete-time-systems-and-safety/discrete-time-dynamical-system.md)

## Proof depends on

None.

## Expansion

Global asymptotic stability is the property whose decision problem is undecidable for saturated linear systems and for linear plants with ReLU neural-network feedback, the cases treated on the theorem pages of this topic.

## Sources

- Milan Korda, "Stability and performance verification of dynamical systems controlled by neural networks: algorithms and complexity", *IEEE Control Systems Letters* 6, 2022, pp. 3265–3270, <https://doi.org/10.1109/LCSYS.2022.3181806>; read as arXiv:2102.02273v5, <https://arxiv.org/abs/2102.02273v5>: the definition of stability (Definition 1, "Stability") in Section 3 of that version, for the closed-loop system of Section 2.
