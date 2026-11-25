# A policy's Bellman operator is $\gamma$-Lipschitz in the sup norm

Let $M$ be a Markov decision process with finitely many states, and with rewards $r(s, a)$ and
stochastic transition probabilities $p(s, a, s')$ (nonnegative, each row summing to $1$) in a
linearly ordered field $K$, and let $\gamma \ge 0$ in $K$. Let $\pi$ be a deterministic stationary policy with
[Bellman operator](policy-bellman.md) $T_\pi$. If two value estimates $V, W : S \to K$ satisfy
$|V(s') - W(s')| \le d$ for every state $s'$, then $|(T_\pi V)(s) - (T_\pi W)(s)| \le \gamma d$ for
every state $s$.
