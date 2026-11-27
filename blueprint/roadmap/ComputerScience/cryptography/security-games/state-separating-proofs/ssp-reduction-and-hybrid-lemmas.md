# Reduction, hybrid and state-simulation lemmas for packages

(i) *Reduction:* for a package $R$ and closed packages $M_0, M_1$, distinguishing $R \circ M_0$ from $R \circ M_1$ with adversary $\mathcal{A}$ has the same advantage as distinguishing $M_0$ from $M_1$ with the linked adversary $\mathcal{A} \circ R$. (ii) *Hybrid:* for closed packages $M_0, \dots, M_k$, the advantage between $M_0$ and $M_k$ is at most the sum of the advantages between consecutive packages. (iii) *State simulation:* if every state of $M$ is represented by a state of $M'$ such that initial distributions correspond and every oracle call maps represented states to represented states with the same outputs, then $\mathcal{A}^M$ and $\mathcal{A}^{M'}$ have the same output distribution. (iv) *Lazy initialization:* running parallel sessions whose states are initialized on first use gives the same distribution as initializing all sessions eagerly.

## Proof sketch

(i) is associativity of composition; (ii) is the triangle inequality; (iii) is an induction on the adversary's program; (iv) follows from independence of the session initializations.

## Depends on

- [Packages and composition in state-separating proofs](ssp-packages.md)

## Proof depends on

- [Hybrid argument](../games-and-advantages/advantage-le-sum.md)

## Sources

- Chris Brzuska et al., "State Separation for Code-Based Game-Playing Proofs", Advances in Cryptology – ASIACRYPT 2018, 2018.
