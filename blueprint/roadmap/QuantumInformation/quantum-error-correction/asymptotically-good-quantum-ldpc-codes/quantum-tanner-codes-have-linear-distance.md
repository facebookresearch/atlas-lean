# Leverrier-Zemor: quantum Tanner codes are asymptotically good

Fix $\rho \in (0, 1/2)$, $\epsilon \in (0, 1/2)$, $\gamma \in (1/2 + \epsilon, 1)$ and $\delta > 0$, and let $\Delta$ be large enough. Let the Cayley graphs $\mathrm{Cay}(G, A)$ and $\mathrm{Cay}(G, B)$ be $\Delta$-regular Ramanujan graphs (every eigenvalue other than $\pm\Delta$ has modulus at most $2\sqrt{\Delta - 1}$), and let $C_A, C_B \subseteq \mathbb{F}_2^{\Delta}$ satisfy:

1. $0 < \dim C_A \le \rho\Delta$ and $\dim C_B = \Delta - \dim C_A$;
2. $C_A$, $C_B$, $C_A^\perp$ and $C_B^\perp$ all have minimum distance at least $\delta\Delta$;
3. both dual tensor codes $C_A^\perp \boxplus C_B^\perp = (C_A \otimes C_B)^\perp$ and $C_A \boxplus C_B = (C_A^\perp \otimes C_B^\perp)^\perp$ are $\Delta^{3/2 - \epsilon/2}$-robust with $\Delta^{\gamma}$-resistance to puncturing. Here a dual tensor code $C \boxplus C'$ is $w$-robust if the support of each of its codewords $x$ with $|x| \le w$ lies in the union of $|x|/d(C)$ columns and $|x|/d(C')$ rows, and it has $p$-resistance to puncturing if it stays $w$-robust after puncturing to $A' \times B'$ for all $A' \subseteq A$, $B' \subseteq B$ with $|A'| = |B'| = \Delta - w'$ and $w' \le p$.

Then $\mathrm{QT}(G, A, B, C_A, C_B)$ is a quantum LDPC code with

$$
k \ge (1 - 2\rho)^2 n, \qquad d \ge \frac{\delta}{4\Delta^{3/2 + \epsilon}}\, n .
$$

The relative distance $\beta(\Delta) = \delta/(4\Delta^{3/2+\epsilon})$ depends on $\Delta$; it is a positive constant for each fixed $\Delta$, not uniform in $\Delta$. For every $\Delta = q + 1$ with $q$ an odd prime power there are infinite families of such Ramanujan left-right Cayley complexes, over the groups $\mathrm{PSL}_2(q^i)$, and when $0 < \delta < 1/2$ and $-\delta\log_2\delta - (1-\delta)\log_2(1-\delta) < \rho$, random $C_A, C_B$ of dimensions $\lfloor\rho\Delta\rfloor$ and $\Delta - \lfloor\rho\Delta\rfloor$ satisfy conditions 1-3 with positive probability for $\Delta$ large. This gives asymptotically good quantum LDPC codes for each such fixed $\Delta$. On the quadripartite variant of the complex, Leverrier and Zémor later replaced condition 3 by $\kappa$-product-expansion of both $(C_A, C_B)$ and $(C_A^\perp, C_B^\perp)$ (with the distance bound in condition 2), obtaining $d > \delta^2\kappa^2 n/(256\Delta)$ for $\Delta$ large enough.

## Proof sketch

Let $x$ be a $Z$-type logical of small weight, viewed on the squares. Call a vertex of $V_0$ active if its local view of $x$ is nonzero. Robustness of the local dual tensor code decomposes each low-weight local view into a few columns and rows of local codewords, and resistance to puncturing lets one discard the rows and columns shared with the few exceptional (high-degree) vertices; the expander mixing lemma on the left and right Cayley graphs shows that if the active set is small, most rows and columns are shared with neighbouring active vertices, allowing one to subtract $X$-checks (local codewords of $C_A \otimes C_B$) to reduce $|x|$ strictly. Iterating shows that a minimal-weight representative of a nontrivial logical has linear weight. The $X$-distance is symmetric with the roles of codes dualized. Existence follows from random local codes, which are robust with resistance to puncturing with high probability, and explicit Ramanujan left-right Cayley complexes over $\mathrm{PSL}_2(q^i)$.

## Depends on

- [Quantum Tanner codes](quantum-tanner-codes.md)
- [Tensor codes and dual tensor codes](tensor-codes-and-dual-tensor-codes.md)
- [Product-expansion of a pair of codes](product-expansion-of-a-pair-of-codes.md)

## Proof depends on

- [Quantum Tanner checks commute](commutation-of-quantum-tanner-checks.md)
- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641v3 (Theorems 1, 2, 17 and 18).
- Anthony Leverrier, Gilles Zemor, "Decoding quantum Tanner codes", IEEE Transactions on Information Theory 69 (2023); arXiv:2208.05537 (Theorems 1 and 9).
