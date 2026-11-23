# Optimal rate of Nesterov's scheme started at $\gamma_0 = L$

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ differentiable and $\mu$-strongly convex with $L$-Lipschitz gradient, where $L > 0$ and $0 \le \mu \le L$, and let $x^*$ minimise $f$. If the sequences follow [Nesterov's general scheme](is-nesterov-scheme.md) with $\gamma_0 = L$, then for every $k$,

$$
f(x_k) - f(x^*) \le L \min\Big\{\Big(1 - \sqrt{\mu / L}\Big)^k,\ \frac{4}{(k + 2)^2}\Big\}\, \|x_0 - x^*\|^2 .
$$

This is exactly the inequality of the source. For $\mu = 0$ (plain convexity) it is the accelerated rate $4L\|x_0 - x^*\|^2/(k+2)^2$, against $O(L\|x_0 - x^*\|^2/k)$ for gradient descent. It is within the constant factor $128/3$ of the [lower complexity bound](../lower-complexity-bounds-for-first-order-methods/exists-lower-bound-smooth-convex.md) $3L\|x_0 - x^*\|^2/(32(k+1)^2)$ (valid while $2k + 1 \le n$ in dimension $n$), which is the sense in which the source calls the scheme optimal.

The proof combines the [convergence theorem](estimate-sequence-rate.md) at $u = x^*$, the [decay of $\lambda_k$](estimate-sequence-lambda-le.md) with $\gamma_0 = L$ (for which $4L/(2\sqrt{L} + k\sqrt{L})^2 = 4/(k+2)^2$), and the bound $f(x_0) - f(x^*) \le \frac{L}{2}\|x_0 - x^*\|^2$, which follows from the [descent lemma](../gradient-descent/gradient-descent-descent-lemma.md) at $x^*$, where $\nabla f(x^*) = 0$.

## Informally uses

- [Convergence of Nesterov's estimate-sequence scheme](estimate-sequence-rate.md): the bound $f(x_k) - f(x^*) \le \lambda_k(f(x_0) - f(x^*) + \frac{L}{2}\|x_0 - x^*\|^2)$.
- [Decay of the scaling sequence of Nesterov's scheme](estimate-sequence-lambda-le.md): both bounds on $\lambda_k$.
- [Descent lemma](../gradient-descent/gradient-descent-descent-lemma.md): $f(x_0) \le f(x^*) + \frac{L}{2}\|x_0 - x^*\|^2$.

## Background

- [Nesterov's $O(1/k^2)$ rate for accelerated gradient descent](nesterov-accelerated-rate.md): the same order of rate for the three-sequence method, proved with the Lyapunov function of Wilson, Recht and Jordan; its constant $2L/(k(k+1))$ is smaller than $4L/(k+2)^2$ for $k \ge 4$, for a different method.
- [Lower complexity bound for smooth convex minimisation](../lower-complexity-bounds-for-first-order-methods/exists-lower-bound-smooth-convex.md): the bound that this rate matches up to a constant.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Theorem 2.2.2 (the inequality; the optimality discussion in its proof uses Theorems 2.1.6 and 2.1.12).
