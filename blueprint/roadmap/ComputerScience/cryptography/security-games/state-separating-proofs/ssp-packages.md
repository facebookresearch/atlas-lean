# Packages and composition in state-separating proofs

In *state-separating proofs*, a *package* is a stateful probabilistic program with an exported interface (oracles it offers) and an imported interface (oracles it calls), together with an initial distribution on its state. Packages compose *sequentially*, $P \circ Q$, by answering the imports of $P$ with the exports of $Q$, and *in parallel*, $P \parallel Q$, by placing them side by side with disjoint states; $\mathrm{par}_m(P)$ runs $m$ independent sessions of $P$. A *closed* package has no imports; a *game* is a closed package and an *adversary* is a program calling its exports and outputting a bit. The advantage of $\mathcal{A}$ in distinguishing closed packages $M_0$ and $M_1$ is $|\Pr[\mathcal{A}^{M_0} = 1] - \Pr[\mathcal{A}^{M_1} = 1]|$.

## Depends on

- [Adaptive oracle algorithms](../oracle-algorithms/oracle-comp.md)
- [Distinguishing advantage](../games-and-advantages/advantage.md)

## Sources

- Chris Brzuska et al., "State Separation for Code-Based Game-Playing Proofs", Advances in Cryptology – ASIACRYPT 2018, 2018.
