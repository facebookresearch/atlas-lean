# Expected transition counts of a finite Markov chain up to a hitting time

Let $X$ be the [path](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) of a continuous-time Markov chain with rate matrix $Q$ on a finite set $S$, let $A \subseteq S$ with [hitting time](ctmc-hitting-time.md) $\tau = H_A$
satisfying $\mathbb E_k \tau < \infty$, and for $i \ne j$ let $N_{ij}(\tau)$ be the number of jumps from $i$ to $j$ at times at most $\tau$. Then

$$\mathbb E_k N_{ij}(\tau) = Q_{ij}\, \mathbb E_k \int_0^\tau \mathbf 1\{X_s = i\}\, ds .$$

For $i \in A$ both sides are $0$. If $i \notin A$ and $q(i)=0$, then $Q_{ij}=0$ and the chain never jumps out of $i$, so both sides are again $0$. For $i \notin A$ with $q(i)>0$, let $V_i$ be the expected number of visits of the jump chain to $i$ before it enters $A$. Each visit
leaves for $j$ with probability $Q_{ij}/q(i)$, by the [jump matrix](../finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md), and lasts an exponential time of mean $1/q(i)$ independent of the jump chain. So the left side
is $V_i\, Q_{ij}/q(i)$ and the occupation time has mean $V_i/q(i)$; both are finite because $\mathbb E_k \tau < \infty$, which the [backward equations](ctmc-hitting-time-backward.md) can certify.
Summing over $j \ne i$ gives the expected number of jumps out of $i$ as $q(i)$ times the occupation time. For two states with $A = \{1\}$ started at $0$,
there is one jump, and the occupation of $0$ has mean $1/Q_{01}$.

## Depends on

- [Path of a continuous-time Markov chain](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
- [Hitting time of a continuous-time Markov chain](ctmc-hitting-time.md)

## Proof depends on

- [Jump matrix of a rate matrix](../finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md)

## Related topics

- [Backward equations for the mean hitting time](ctmc-hitting-time-backward.md)

## Sources

- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), Chapter 2. The identity is derived above.
