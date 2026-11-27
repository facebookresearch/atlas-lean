# Reduction, hybrid and state-simulation lemmas for packages

(i) *Reduction:* for a package $R$ and closed packages $M_0, M_1$ with $\mathrm{in}(R) \subseteq \mathrm{out}(M_b)$, distinguishing $R \circ M_0$ from $R \circ M_1$ with adversary $\mathcal{A}$ has the same advantage as distinguishing $M_0$ from $M_1$ with the linked adversary $\mathcal{A} \circ R$ (Brzuska et al., Lemma 15). (ii) *Hybrid:* for closed packages $M_0, M_1, M_2$ with the same oracles, the advantage between $M_0$ and $M_2$ is at most the sum of the advantages between $M_0$ and $M_1$ and between $M_1$ and $M_2$ (Brzuska et al., Lemma 14). (iii) *State simulation:* let $\psi$ be a relation between the states of closed packages $M_0$ and $M_1$ that constrains only their own state variables and holds on their initial states. If for every oracle $f$ and argument $a$ and every pair of $\psi$-related states, the two executions of $f(a)$ have a coupling under which the outputs are equal and the final states are again $\psi$-related, then every adversary has advantage $0$ in distinguishing $M_0$ from $M_1$ (Haselwarter et al., Theorem 2.4).

## Proof sketch

(i) is associativity of sequential composition (Brzuska et al., Lemma 6); (ii) is the triangle inequality, and applied repeatedly it bounds the advantage between $M_0$ and $M_k$ by the sum of the advantages between consecutive packages of a chain $M_0, \dots, M_k$; (iii) is an induction on the adversary's oracle calls that keeps the two executions coupled with equal answers and $\psi$-related states (Haselwarter et al., Section 4.2).

## Depends on

- [Packages and composition in state-separating proofs](ssp-packages.md)
- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Proof depends on

- [Hybrid argument](../games-and-advantages/advantage-le-sum.md)

## Sources

- Chris Brzuska et al., "State Separation for Code-Based Game-Playing Proofs", Advances in Cryptology – ASIACRYPT 2018, 2018, Lemmas 6, 14 and 15 (numbered as in the full version, Cryptology ePrint Archive, Paper 2018/306).
- Philipp G. Haselwarter, Exequiel Rivas, Antoine Van Muylder, Théo Winterhalter, Carmine Abate, Nikolaj Sidorenco, Cătălin Hriţcu, Kenji Maillard and Bas Spitters, "SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq", ACM Transactions on Programming Languages and Systems 45(3), 2023, Theorem 2.4 and Section 4.2 (numbered as in Cryptology ePrint Archive, Paper 2021/397).
