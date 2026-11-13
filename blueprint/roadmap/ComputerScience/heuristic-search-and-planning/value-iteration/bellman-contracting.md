# Bellman's operator is a contraction

Let $M$ be a Markov decision process with finitely
many states, a nonempty finite set of actions, real rewards and stochastic transition
probabilities, and let $0 \le \gamma < 1$. Then the Bellman optimality operator $T$ of $M$ with
discount $\gamma$, acting on real-valued functions on the states with the sup metric, is a
contraction with constant $\gamma$: for all such functions $V$ and $W$,
$\|TV - TW\|_\infty \le \gamma \|V - W\|_\infty$.

## Sources

- Puterman, Theorem 6.2.3.
