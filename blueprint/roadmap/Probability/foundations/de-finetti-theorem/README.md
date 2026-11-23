# De Finetti's theorem for binary sequences

Let $\mu$ be a probability measure on the space $\{0, 1\}^{\mathbb{N}}$ of binary sequences $\omega = (\omega_i)_{i \in \mathbb{N}}$, with its product σ-algebra. Suppose $\mu$ is exchangeable: for every permutation $\pi$ of $\mathbb{N}$ that moves only finitely many points, the image of $\mu$ under the map $\omega \mapsto \omega \circ \pi$ is $\mu$. Then there is a probability measure $\nu$ on $[0, 1]$ such that for all disjoint finite sets $A, B \subseteq \mathbb{N}$, the probability under $\mu$ that $\omega_i = 1$ for all $i \in A$ and $\omega_i = 0$ for all $i \in B$ equals $\int_{[0, 1]} p^{|A|} (1 - p)^{|B|} \, d\nu(p)$.

## Idea

An exchangeable infinite sequence of coin tosses is a mixture of independent ones: first draw a bias $p$ from $\nu$, then toss a coin with bias $p$ independently forever. In Bayesian terms, a belief that treats the order of the tosses as irrelevant is the same as a prior $\nu$ on an unknown bias. The measure $\nu$ is the law of the limiting frequency $\lim_n (\omega_0 + \dots + \omega_{n-1}) / n$. For example, the colours drawn from a Pólya urn that starts with one red and one blue ball, each drawn ball being returned with one more of its colour, form an exchangeable sequence whose mixing measure is the uniform law on $[0, 1]$. The infinite length matters: drawing both balls without replacement from an urn with one red and one blue ball gives an exchangeable pair that is no such mixture, since neither colour can appear twice.

## Statements

- [De Finetti's theorem for binary sequences](de-finetti-binary.md)

## Sources

- B. de Finetti, *Funzione caratteristica di un fenomeno aleatorio*, 1931.
