# Action values are $\gamma$-Lipschitz in the value estimate

Let $M$ be a Markov decision process with finitely many states, and with rewards $r(s, a)$ and
stochastic transition probabilities $p(s, a, s')$ (nonnegative, each row summing to $1$) in a
linearly ordered field $K$, and let $\gamma \ge 0$ in $K$. If two value estimates $V, W : S \to K$ satisfy
$|V(s') - W(s')| \le d$ for every state $s'$, then for every state $s$ and action $a$ the
[Q-values](q-value.md) satisfy

$$\Bigl|\Bigl(r(s, a) + \gamma \sum_{s'} p(s, a, s') V(s')\Bigr) - \Bigl(r(s, a) + \gamma \sum_{s'} p(s, a, s') W(s')\Bigr)\Bigr| \le \gamma d.$$
