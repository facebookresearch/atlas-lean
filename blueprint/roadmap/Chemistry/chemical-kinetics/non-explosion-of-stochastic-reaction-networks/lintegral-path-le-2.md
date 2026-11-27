# Fixed-time Lyapunov moment bound for a stochastic reaction network

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, [generator](generator.md) $L$ and
[total propensity](total-rate.md) $\lambda$. Let $V : \mathbb{N}^S \to [0, \infty)$ and $c \ge 0$
satisfy:

- $L V(x) \le c\, V(x)$ at every state $x$;
- for every real $m$ there is a $K$ with $\lambda(x) \le K$ for all states $x$ with $V(x) < m$.

Let the step sequence have the [law of the steps](input-measure-2.md) $\mathbb{P}$, a probability
measure, and let $X_t$ be the [path](path-2.md) started at $x_0 \in \mathbb{N}^S$. Then for every
$t \ge 0$,

$$\mathbb{E}\bigl[V(X_t)\bigr] \le e^{c t}\, V(x_0),$$

where $\mathbb{E}$ is the lower Lebesgue integral with respect to $\mathbb{P}$, a value in
$[0, \infty]$, here finite.
