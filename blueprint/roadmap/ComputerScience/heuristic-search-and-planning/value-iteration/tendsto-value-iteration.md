# Value iteration converges

Let $M$ be a Markov decision process with finitely many states
$S$, a nonempty finite set of actions, real rewards and stochastic transition probabilities
(nonnegative, each row summing to $1$), and let $0 \le \gamma < 1$ be a discount factor. Let $T$ be
the Bellman optimality operator of $M$ with discount $\gamma$. Then for every initial value
function $V : S \to \mathbb{R}$, the value iterates $T^n V$ converge to the optimal value of $M$
with discount $\gamma$ as $n \to \infty$.
