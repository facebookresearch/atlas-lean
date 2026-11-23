# Decay of the scaling sequence of Nesterov's scheme

If the sequences follow [Nesterov's general scheme](is-nesterov-scheme.md) with $L > 0$ and $0 \le \mu \le \gamma_0$, then $\lambda_k = \prod_{i < k} (1 - \alpha_i)$ satisfies

$$
\lambda_k \le \Big(1 - \sqrt{\mu / L}\Big)^k
\qquad\text{and}\qquad
\lambda_k \le \frac{4L}{\big(2\sqrt{L} + k\sqrt{\gamma_0}\big)^2}.
$$

The source states the minimum of the two bounds, which is the same statement. The first bound comes from $\gamma_k \ge \mu$, hence $\alpha_k \ge \sqrt{\mu/L}$; the second from $\gamma_k \ge \gamma_0 \lambda_k$, which gives $\lambda_{k+1}^{-1/2} - \lambda_k^{-1/2} \ge \frac{1}{2}\sqrt{\gamma_0 / L}$. One proof bounds $\sqrt{\lambda_k}\,(2\sqrt{L} + k\sqrt{\gamma_0})$ by $2\sqrt{L}$ by induction, treating separately the case $\lambda_{k+1} = 0$ that $\alpha_k = 1$ allows.

## Informally uses

- [Nesterov's general optimal scheme](is-nesterov-scheme.md): only the recursions for $\alpha_k$ and $\gamma_k$ are used.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Lemma 2.2.4.
