# Leverrier-Zemor: quantum Tanner codes are asymptotically good

For every $\rho \in (0, 1/2)$ there are $\Delta_0$ and $\beta > 0$ such that the following holds for $\Delta \ge \Delta_0$. If the Cayley graphs $\mathrm{Cay}(G, A)$ and $\mathrm{Cay}(G, B)$ are $\Delta$-regular with second largest eigenvalue modulus at most $c_0\sqrt{\Delta}$ for an absolute constant $c_0$ (for instance Ramanujan-type families), $C_A$ has rate $\rho$, $C_B$ has rate $1 - \rho$, and both $(C_A, C_B)$ and $(C_A^\perp, C_B^\perp)$ are product-expanding with parameter bounded below, then $\mathrm{QT}(G, A, B, C_A, C_B)$ is a quantum LDPC code with

$$
k \ge (1 - 2\rho)^2 n, \qquad d \ge \beta\, n .
$$

Infinite families of such complexes and local codes exist, giving asymptotically good quantum LDPC codes.

## Proof sketch

Let $x$ be a $Z$-type logical of small weight, viewed on the squares. Call a vertex of $V_0$ active if its local view of $x$ is nonzero. Product-expansion decomposes each local view into a few columns and rows of local codewords; the expander mixing lemma on the left and right Cayley graphs shows that if the active set is small, most rows and columns are shared with neighbouring active vertices, allowing one to subtract $X$-checks (local codewords of $C_A \otimes C_B$) to reduce $|x|$ strictly. Iterating shows that a minimal-weight representative of a nontrivial logical has linear weight. The $X$-distance is symmetric with the roles of codes dualized. Existence follows from random local codes and explicit Ramanujan Cayley graphs, for instance from $\mathrm{PSL}_2(\mathbb{F}_q)$ with Lubotzky-Phillips-Sarnak generators.

## Depends on

- [Quantum Tanner codes](quantum-tanner-codes.md)
- [Product-expansion of a pair of codes](product-expansion-of-a-pair-of-codes.md)

## Proof depends on

- [Quantum Tanner checks commute](commutation-of-quantum-tanner-checks.md)
- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
