# Monotone span programs and linear secret sharing

A *monotone span program* over a finite field $\mathbb{F}$ assigns to each party $P$ a matrix $M_P \in \mathbb{F}^{d_P \times d}$ (equivalently, a single matrix whose rows are labeled by parties). It *accepts* a coalition $S$ if the target vector $e_1 = (1, 0, \dots, 0)$ lies in the row span of the stacked matrix $M_S$ of its members. The accepted coalitions form a monotone access structure: a superset of an accepted coalition is accepted. The *linear secret-sharing scheme* of the program shares $z \in \mathbb{F}$ with a uniform $\rho \in \mathbb{F}^{d-1}$ (uniform because $\mathbb{F}$ is finite) by giving party $P$ the vector $M_P\,(z, \rho)^{\mathsf T}$. An accepted coalition reconstructs $z = \sum \lambda \cdot \sigma$ for any recombination vector $\lambda$ with $\lambda^{\mathsf T} M_S = e_1$. Two programs are *equivalent* if for every secret their schemes give the same distribution of shares.

## Sources

- Amos Beimel, "Secret-Sharing Schemes: A Survey", Coding and Cryptology, Lecture Notes in Computer Science, Springer, 2011, pp. 11–46, Section 3.5, Definition 4 and Claim 2.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023 (equivalence of programs).
