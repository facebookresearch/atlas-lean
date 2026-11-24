# Least-fixpoint soundness of abstract interpretation

Let $\Sigma$ be a type of states, let $\sqsubseteq$ be any complete lattice order on the sets of states $\mathcal{P}(\Sigma)$ (not necessarily inclusion), and let $(A, \le)$ be a complete lattice. Let $\alpha : \mathcal{P}(\Sigma) \to A$ and $\gamma : A \to \mathcal{P}(\Sigma)$ form a Galois connection: $\alpha(X) \le a$ if and only if $X \sqsubseteq \gamma(a)$, for all $X$ and $a$. Let $F : \mathcal{P}(\Sigma) \to \mathcal{P}(\Sigma)$ and $F^\sharp : A \to A$ be monotone (for $\sqsubseteq$ and $\le$ respectively), and assume the transfer condition $\alpha(F(\gamma(a))) \le F^\sharp(a)$ for every $a \in A$. Then

$$\alpha(\operatorname{lfp} F) \le \operatorname{lfp} F^\sharp,$$

where $\operatorname{lfp}$ denotes the least fixed point of a monotone map on a complete lattice.

## Sources

- P. Cousot and R. Cousot, POPL 1977 (the lattice framework of abstract interpretation).
