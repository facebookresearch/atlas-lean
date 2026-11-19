# A greedy policy's Bellman update is the optimal update

Let $M$ be a Markov decision process with finitely many states, a nonempty finite set of actions,
and rewards and transition probabilities in a field $K$ with a linear order, and let $\gamma \in K$.
For every value estimate $V : S \to K$, the [Bellman operator](policy-bellman.md) of the
[greedy policy](greedy.md) for $V$, applied to $V$, equals the
[Bellman optimality operator](bellman.md) applied to $V$: $T_{\mathrm{greedy}(V)} V = TV$. No
condition on the transition probabilities or on $\gamma$ is needed.
