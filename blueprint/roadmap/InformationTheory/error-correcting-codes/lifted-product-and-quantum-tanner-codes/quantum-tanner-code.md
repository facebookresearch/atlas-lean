# Quantum Tanner codes on left-right Cayley complexes

Let $X = \mathrm{Cay}^2(A, G, B)$ be a left-right Cayley complex and assume it is bipartite on vertices, $G = V_0 \sqcup V_1$, with both Cayley graphs edge-bipartite with respect to this partition. Qubits are placed on squares. For local codes $C_A \subseteq \mathbb{F}_2^A$ and $C_B \subseteq \mathbb{F}_2^B$, define

$$
C_0 = \{\, f : f_v \in C_A \otimes C_B \ \forall v \in V_0 \,\}, \qquad C_1 = \{\, f : f_v \in C_A^{\perp} \otimes C_B^{\perp} \ \forall v \in V_1 \,\}.
$$

Generators of $(C_A \otimes C_B)^{\perp}$ at $V_0$-vertices give $X$-checks and generators of $(C_A^{\perp} \otimes C_B^{\perp})^{\perp}$ at $V_1$-vertices give $Z$-checks. The local orthogonality of supports at the shared squares makes this a CSS code, the **quantum Tanner code** $\mathrm{QT}(X, C_A, C_B)$.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](../../../QuantumInformation/quantum-error-correction/homological-quantum-ldpc-codes/quantum-ldpc-code-families-and-good-codes.md)
- [Tensor codes on the squares of a left-right Cayley complex](../left-right-cayley-complex-codes/square-complex-tensor-code.md)

## Sources

- A. Leverrier, G. Zémor, "Quantum Tanner codes", FOCS (2022), arXiv:2202.13641.
