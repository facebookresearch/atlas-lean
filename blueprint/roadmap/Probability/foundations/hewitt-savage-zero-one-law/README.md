# Hewitt–Savage zero–one law

Let $\mu$ be a probability measure on a measurable space $S$, and let $E \subseteq S^{\mathbb{N}}$ be a set that is measurable for the product σ-algebra and invariant under every permutation $\sigma$ of $\mathbb{N}$ that moves only finitely many points, that is, $\{\omega : \omega \circ \sigma \in E\} = E$. Then $E$ has measure $0$ or $1$ under the product measure $\mu^{\otimes \mathbb{N}}$. No topological assumption on $S$ is needed.

## Idea

For an i.i.d. sequence, every event that is unchanged when finitely many terms are shuffled is trivial. This covers more than tail events: for a random walk $S_n = X_1 + \dots + X_n$ with real i.i.d. steps, the event that $S_n = 0$ for infinitely many $n$ is not a tail event, but it is unchanged by permutations of finitely many steps, so its probability is $0$ or $1$. The proof shows that $\mu^{\otimes \mathbb{N}}(E)$ equals its own square. Approximate $E$ by an event $A_n$ depending only on the first $n$ coordinates; the permutation exchanging the first $n$ coordinates with the next $n$ fixes $E$ and carries $A_n$ to an event independent of $A_n$ that also approximates $E$, so $\mu^{\otimes \mathbb{N}}(E)$ is close to $\mu^{\otimes \mathbb{N}}(A_n)^2$.

## Statements

- [Hewitt–Savage zero–one law](hewitt-savage-zero-one-general.md)
- [Exchangeable event](is-exchangeable-event.md): definition used by the i.i.d. form
- [Event exchangeable with respect to a sequence](is-exchangeable-event-wrt.md): definition used by the i.i.d. form
- [Exchangeable events of a measurable sequence are measurable](measurable-set.md): basic property of exchangeable events
- [Hewitt–Savage zero–one law on a Polish space](hewitt-savage-zero-one.md): Polish-space special case
- [Hewitt–Savage zero–one law for i.i.d. sequences](hewitt-savage-zero-one-2.md): form for i.i.d. sequences of random variables

## Sources

- E. Hewitt and L. J. Savage, *Symmetric measures on Cartesian products*, Transactions of the American Mathematical Society (1955).
