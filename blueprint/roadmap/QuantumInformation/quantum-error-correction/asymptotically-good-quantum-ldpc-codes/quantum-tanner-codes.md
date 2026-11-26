# Quantum Tanner codes

Let $\mathrm{Cay}^2(A, G, B)$ be a left-right Cayley complex with square set $Q$, and let $C_A \subseteq \mathbb{F}_2^A$, $C_B \subseteq \mathbb{F}_2^B$ be linear codes. The *quantum Tanner code* $\mathrm{QT}(G, A, B, C_A, C_B)$ has one qubit per square, $n = |Q| = 2|G|\Delta^2/2 = |G|\Delta^2$, and

- $X$-checks: for every $v \in V_0$ and every $c \in C_A \otimes C_B$, the operator $X^{c}$ supported on the squares of the local view of $v$ according to $c$;
- $Z$-checks: for every $v \in V_1$ and every $c \in C_A^{\perp} \otimes C_B^{\perp}$, the operator $Z^{c}$ on the local view of $v$.

It is LDPC with check weight at most $\Delta^2$ and qubit degree at most $2(\dim C_A \dim C_B + \dim C_A^\perp \dim C_B^\perp)$.

## Depends on

- [Left-right Cayley complexes](../../../InformationTheory/error-correcting-codes/left-right-cayley-complex-codes/left-right-cayley-complex.md)
- [Tensor codes and dual tensor codes](tensor-codes-and-dual-tensor-codes.md)
- [The CSS code of a chain complex](../homological-quantum-ldpc-codes/css-code-of-a-chain-complex.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
