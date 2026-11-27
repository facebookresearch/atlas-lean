# Running sums of the expected payoffs of a strategy

Let $A$ be a finite set of actions, $B$ a set of opponent actions, $E$ a real inner product space,
$v : A \times B \to E$ a vector payoff, $\sigma$ a map from $E$ to weight vectors on $A$ (mixed actions in
the intended use) and $\beta = (\beta_k)_{k \ge 0}$ a sequence of opponent actions. The running sums are
defined by $S_0 = 0$ and

$$S_{n+1} = S_n + v\bigl(\sigma(S_n / n), \beta_n\bigr),$$

with $S_n / n = 0$ for $n = 0$: the decision maker plays $\sigma(\bar x)$ at the current average $\bar x$ of
the past expected payoffs, and $S_n = \sum_{k < n} v(\sigma(\bar x_k), \beta_k)$.
