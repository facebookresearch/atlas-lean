# Holenstein's correlated sampling from a distribution-independent seed

Two parties hold distributions $P$ and $Q$ on a finite set $\Omega$ and share an i.i.d. sequence $(x_n, u_n)$ of uniform points of $\Omega \times [0,1]$, whose law does not depend on $P$ or $Q$. Each party outputs the first $x_n$ with $u_n < P(x_n)$ (respectively $Q(x_n)$). Then each output has exactly the party's own distribution, and the outputs differ with probability at most $2\delta/(1 + \delta) \le 2\delta$, where $\delta$ is the statistical distance between $P$ and $Q$.

(Finite seed.) If all probabilities are multiples of $1/L$, a party with counts $c(x) = L\,P(x)$ owns the $L$ cells $\{(x, u) : u < c(x)\} \subseteq \Omega \times \{0, \dots, L-1\}$; with a shared uniformly random ordering of $\Omega \times \{0,\dots,L-1\}$ as seed, outputting the point of one's first own cell samples one's own distribution exactly and disagrees with the other party with probability at most $2\delta$.

## Proof sketch

The first point of an i.i.d. sequence lying in a region of positive probability is distributed as one point conditioned on the region; under the graph of $P$ its first coordinate has law $P$. If the first point under the graph of $\max(P, Q)$ lies under $\min(P, Q)$, both parties output it; the two regions have areas $(1 + \delta)/|\Omega|$ and $(1 - \delta)/|\Omega|$.

## Depends on

- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing, 2009.
