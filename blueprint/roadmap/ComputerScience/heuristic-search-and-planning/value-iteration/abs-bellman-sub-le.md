# The Bellman operator contracts by $\gamma$

Let $M$ be a Markov decision process with
finitely many states, a nonempty finite set of actions, and rewards and stochastic transition
probabilities in a linearly ordered field $K$, let $\gamma \ge 0$ in $K$, and let $T$ be the
Bellman optimality operator of $M$ with discount $\gamma$. If two functions $V, W$ from states
to $K$ satisfy $|V(s) - W(s)| \le d$ for every state $s$, where $d \in K$, then
$|(TV)(s) - (TW)(s)| \le \gamma d$ for every state $s$.
