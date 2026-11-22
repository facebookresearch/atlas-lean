# De Finetti's theorem for binary sequences

Let $\mu$ be a probability measure on the space
$\{0, 1\}^{\mathbb{N}}$ of binary sequences $\omega = (\omega_i)_{i \in \mathbb{N}}$, with $0$ and
$1$ standing for false and true. Suppose $\mu$ is exchangeable: for every permutation $\pi$ of
$\mathbb{N}$ that moves only finitely many points, the image of $\mu$ under the map
$\omega \mapsto \omega \circ \pi$ is $\mu$. Then there is a probability measure $\nu$ on $[0, 1]$
such that for all disjoint finite sets $A, B \subseteq \mathbb{N}$,

$$\mu\{\omega : \omega_i = 1 \text{ for all } i \in A \text{ and } \omega_i = 0 \text{ for all }
i \in B\} = \int_{[0, 1]} p^{|A|} (1 - p)^{|B|} \, d\nu(p).$$

## Sources

- B. de Finetti, Funzione caratteristica di un fenomeno aleatorio, Atti Accad. Naz. Lincei 4 (1931) and La prévision: ses lois logiques (1937); textbook in Kallenberg, Probabilistic Symmetries and Invariance Principles; also Durrett, Probability Theory and Examples
