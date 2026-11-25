# Linear-chain conditional random field

Let $S$ be a type of states, $O$ a type of inputs
and $R$ a type of weights with a zero and a relation $\le$. A linear-chain conditional random
field consists of a unary potential $\phi(x, t, s) \in R$ and a transition potential
$\psi(x, t, s, s') \in R$ from $s$ to $s'$, given for every observation sequence
$x \colon \mathbb{N} \to O$, every position $t \in \mathbb{N}$ and all states $s, s' \in S$, such
that $0 \le \phi(x, t, s)$ and $0 \le \psi(x, t, s, s')$ always hold.

Both potentials see the whole, possibly infinite, observation sequence $x$, so path weights
condition on all of $x$, as the conditional probability $p(y \mid x)$ of a label sequence $y$
does in the standard definition. Nonnegativity makes the potentials unnormalized
probabilities.
