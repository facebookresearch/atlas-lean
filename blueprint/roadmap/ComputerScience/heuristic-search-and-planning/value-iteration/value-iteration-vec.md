# Tabulated value iteration

Let $M$ be a Markov decision process with states
$\{0, \dots, m-1\}$, a nonempty finite set of actions, and rewards and transition probabilities
in a field $K$ carrying a linear order, let $\gamma \in K$, and let $T$ be the Bellman optimality
operator of $M$ with discount $\gamma$. Tabulated value iteration takes a number of steps
$n \in \mathbb{N}$ and a vector $v \in K^m$, read as a function on states: with $0$ steps it
returns $v$, and with $k + 1$ steps it computes the vector $\bigl((Tv)(0), \dots, (Tv)(m-1)\bigr)$
and then runs $k$ steps from that vector.

Each update is stored as a vector, so update $k + 1$ reads the stored values of update $k$.
