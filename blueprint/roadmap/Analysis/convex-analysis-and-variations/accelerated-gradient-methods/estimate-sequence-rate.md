# Convergence of Nesterov's estimate-sequence scheme

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ differentiable and $\mu$-strongly convex with $\mu \ge 0$, and $L > 0$. If the sequences follow [Nesterov's general scheme](is-nesterov-scheme.md), then for every $u \in E$ and every $k$,

$$
f(x_k) - f(u) \le \lambda_k \Big(f(x_0) - f(u) + \tfrac{\gamma_0}{2}\|x_0 - u\|^2\Big), \qquad \lambda_k = \prod_{i < k} (1 - \alpha_i).
$$

The source states this for $u = x^*$, a minimiser of $f$; the statement here holds for every point $u$ and needs no minimiser, so it is slightly stronger. The rate of the method is the rate at which $\lambda_k \to 0$: see [the decay of the scaling sequence](estimate-sequence-lambda-le.md).

## Informally uses

- [One step of Nesterov's estimate-sequence method contracts its potential](estimate-sequence-step.md): applied at each step and iterated, with $v_0 = x_0$.
- [Nesterov's general optimal scheme](is-nesterov-scheme.md): the hypotheses on the sequences.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Theorem 2.2.1.
