# The stopped step keeps the additive drift bound

Let $D$ carry a probability law, $f : S \times D \to S$ a step map and $V : S \to [0, \infty]$ a level function. If $\mathbb{E}[V(f(x, d))] \le V(x) + \beta$ at every state with $V(x) < c$, then the step map stopped at level $c$ satisfies $\mathbb{E}[V(\text{stopped}(x, d))] \le V(x) + \beta$ at every state $x$; in a frozen state the expectation is $V(x)$ itself.
