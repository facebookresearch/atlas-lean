# Quantum Tanner codes

Let $G$ be a finite group and $A, B \subseteq G$ symmetric generating sets with $|A| = |B| = \Delta$, satisfying the total no-conjugacy condition $ag \ne gb$ for all $g \in G$, $a \in A$, $b \in B$. Consider the bipartite (double-cover) left-right Cayley complex with vertex classes $V_0 = G \times \{0\}$ and $V_1 = G \times \{1\}$, whose $A$-edges join $(g, 0)$ to $(ag, 1)$ and whose $B$-edges join $(g, 0)$ to $(gb, 1)$ for $g \in G$, $a \in A$, $b \in B$, and whose squares are $\{(g, 0), (ag, 1), (gb, 1), (agb, 0)\}$; let $Q$ be its set of squares, and let $C_A \subseteq \mathbb{F}_2^A$, $C_B \subseteq \mathbb{F}_2^B$ be linear codes. Every vertex lies in $\Delta^2$ squares and every square has two vertices in $V_0$. The *quantum Tanner code* $\mathrm{QT}(G, A, B, C_A, C_B)$ has one qubit per square, $n = |Q| = |G|\Delta^2/2$, and

- $X$-checks: for every $v \in V_0$ and every $c \in C_A \otimes C_B$, the operator $X^{c}$ supported on the squares of the local view of $v$ according to $c$;
- $Z$-checks: for every $v \in V_1$ and every $c \in C_A^{\perp} \otimes C_B^{\perp}$, the operator $Z^{c}$ on the local view of $v$.

It is LDPC with check weight at most $\Delta^2$ and qubit degree at most $2(\dim C_A \dim C_B + \dim C_A^\perp \dim C_B^\perp)$.

## Depends on

- [Left-right Cayley complexes](../../../InformationTheory/error-correcting-codes/left-right-cayley-complex-codes/left-right-cayley-complex.md)
- [Tensor codes and dual tensor codes](tensor-codes-and-dual-tensor-codes.md)
- [The CSS code of a chain complex](../homological-quantum-ldpc-codes/css-code-of-a-chain-complex.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
