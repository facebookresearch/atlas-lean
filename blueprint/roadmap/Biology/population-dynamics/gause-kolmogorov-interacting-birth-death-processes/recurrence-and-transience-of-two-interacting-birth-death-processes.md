# Recurrence and transience of two interacting birth–death processes

**Model.** Following the Gause–Kolmogorov approach of encoding species interaction by monotone rate functions, let $\xi(t) = (\xi_1(t), \xi_2(t))$ be the continuous-time Markov chain on $\mathbb{Z}_+^2$ that, from $(x,y)$, jumps to

$$(x+1,y) \text{ at rate } F(x)G(y), \qquad (x,y+1) \text{ at rate } F(y)G(x),$$

and to $(x-1,y)$ (if $x > 0$) or $(x,y-1)$ (if $y > 0$) at rate $1$ each, where $F, G > 0$ on $[0,\infty)$. $F$ governs the free growth of each population and $G$ the interaction: $G \equiv 1$ gives independent copies, decreasing $G$ models competition and increasing $G$ mutual facilitation. Let $\zeta(t)$ be the embedded jump chain.

**Theorem.**

1. Let $F$ be non-increasing with $F(x) \to 0$.
   - (a) If either $G$ is non-increasing with $G(x) \to 0$, or $G$ is non-decreasing with $G(x) \to \infty$ and $F(x-1)G(x) \to 0$, then $\xi$ is positive recurrent.
   - (b) If $G$ is non-decreasing and $F(x)G(x) \to \infty$, then $\xi$ is transient.
2. Let $F$ be non-decreasing with $F(x) \to \infty$. If either $G$ is non-decreasing with $G(x) \to \infty$, or $G$ is non-increasing with $G(x) \to 0$ and $F(x)G(x)$ tends to $0$ or to $\infty$, then $\xi$ is transient.

**Exponential case.** For $F(x) = e^{\alpha x}$ and $G(x) = e^{\beta x}$ the chain is reversible with invariant measure $\exp\big(\alpha\frac{x(x-1)+y(y-1)}{2} + \beta xy\big)$, summable if and only if $\alpha < 0$ and $\alpha + \beta < 0$; hence the condition of part 1(a) is also necessary there.

**Theorem (balanced escape under facilitation).** Suppose $F$ is non-increasing with $F \to 0$, $G$ is non-decreasing with $G \to \infty$, and $F(x)G(x) \to \infty$ (the transient case 1(b)). Then almost surely $\zeta_1(t) = \zeta_2(t)$ for infinitely many $t$. If moreover $F(x+a)G(x+b)/(F(x)G(x)) \to 1$ for all $a,b \in \mathbb{R}$, then for every $\delta \in (0,1)$ the embedded chain eventually stays in the cone $\{\delta x \le y \le \delta^{-1}x\}$: the two populations grow to infinity together.

## Expansion

Positive recurrence is proved with a Lyapunov function and a generalized Foster criterion applied to the embedded chain (the rates are bounded below, so recurrence transfers to the continuous-time chain). Transience uses the converse criterion: a function whose expected increment over a bounded number of steps is uniformly positive outside a compact set, with bounded jumps. The balanced-escape theorem reflects that, when each population's own growth is self-limiting ($F \to 0$) but boosted by the other ($G \to \infty$), the smaller population has the higher birth rate relative to its death rate, which pushes the chain toward the diagonal.

## Sources

- Mikhail Menshikov and Vadim Shcherbakov, "Long term behaviour of two interacting birth-and-death processes", arXiv:1605.09607 (2016), Section 2, Theorems 1 and 2 and the exponential-case discussion before Proposition 1, <https://doi.org/10.48550/arXiv.1605.09607>.
