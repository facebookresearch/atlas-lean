# Value iteration

Let $M$ be a Markov decision process with finitely many states, a
nonempty finite set of actions, and rewards and transition probabilities in a field $K$ carrying
a linear order, let $\gamma \in K$, and let $T$ be the Bellman optimality operator of $M$ with
discount $\gamma$. For $n \in \mathbb{N}$ and a function $V$ from states to $K$, $n$ steps of
value iteration from $V$ give the $n$-fold iterate $T^n V$, where $T^0 V = V$.

Evaluated directly, this definition recomputes earlier iterates; tabulated value iteration
stores each update instead.
