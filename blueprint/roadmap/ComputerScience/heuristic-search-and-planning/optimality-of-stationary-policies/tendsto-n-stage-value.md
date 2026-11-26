# The N-stage values of a Markov policy converge

Let $M$ be a Markov decision process with finitely many states and actions, real rewards and stochastic transitions, and let $0 \le \gamma < 1$. For every Markov policy $\pi$ and every terminal value $V$, the $N$-stage values $T_{\mu_0} \cdots T_{\mu_{N-1}} V$ converge as $N \to \infty$, in the sup norm, to the [value of the Markov policy](markov-value.md); the limit does not depend on $V$.

Consecutive $N$-stage values differ by at most $\gamma^N \max_\mu \|V - T_\mu V\|_\infty$, so the sequence is Cauchy; two terminal values are forgotten at rate $\gamma^N$.

## Informally uses

- [The terminal value is forgotten geometrically](dist-n-stage-value-le.md)
