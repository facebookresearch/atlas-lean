# Circuits of multistationarity

Let $G'$ be a mass-action reaction network with complex set $\mathcal{C}_{G'}$. For a subset $C \subseteq \mathcal{C}_{G'}$, choose for each $y \in C$ a new intermediate species $U(y)$; the *canonical extension* $G'_{ext,C}$ adds the reversible reactions $y \rightleftharpoons U(y)$ for all $y \in C$. A network is *multistationary* if for some positive rate constants some stoichiometric compatibility class contains at least two positive steady states.

**Definition.** For $C' \subseteq \mathcal{C}_{G'}$, the *circuits of multistationarity* of $G'$ relative to $C'$ are the inclusion-minimal subsets $C \subseteq C'$ for which $G'_{ext,C}$ is multistationary; for $C' = \mathcal{C}_{G'}$ they are the circuits of multistationarity of $G'$.

**Proposition (shape independence).** For any $C \subseteq \mathcal{C}_{G'}$, $G'_{ext,C}$ is multistationary if and only if the network obtained by inserting, into reactions $y \to y'$ with $y \in C$, an intermediate $U$ in any of the shapes $y \to U \to y'$, $y \rightleftharpoons U \to y'$ or $y \rightleftharpoons U$ is multistationary. So circuits record which source complexes must be "slowed down" by an intermediate, not how.

**Theorem (partially processive phosphorylation).** Let $n \ge 1$ and $I = \{i_0 = 0 < i_1 < \dots < i_k = n\}$, and let $C_I$ be the network with species $S_0,\dots,S_n,E,F$ and reactions

$$S_j + E \to S_{j+1} + E \ (0 \le j \le n-1), \qquad S_{i_j} + F \to S_{i_{j-1}} + F \ (1 \le j \le k),$$

so the kinase acts distributively one site at a time and the phosphatase removes the blocks of sites between consecutive indices of $I$ at once. If $k \ge 2$, the circuits of multistationarity of $C_I$ are exactly the singletons $\{y\}$ where $y$ ranges over all source complexes except $S_j + E$ for $i_{k-1} \le j \le n-1$ and except $S_{i_1} + F$. If $I = \{0, n\}$, no addition of intermediates makes $C_{\{0,n\}}$ multistationary.

For example, for $I = \{0 < m < n\}$ the circuits are $\{S_0+E\}, \dots, \{S_{m-1}+E\}, \{S_n + F\}$: one intermediate at any of these complexes already creates multistationarity, while intermediates elsewhere never do on their own.

## Depends on

- [Lifting nondegenerate multistationarity to networks with intermediates](lifting-nondegenerate-multistationarity-to-networks-with-intermediates.md)
- [Maximal multistationarity of multisite phosphorylation](../../chemical-reaction-network-theory/maximal-multistationarity-of-multisite-phosphorylation.md)

## Expansion

The networks $C_I$ have binomial steady-state ideals with linear elimination ("lebn") and are monostationary without intermediates. For such networks multistationarity of a canonical extension is decided by sign patterns: one forms a polynomial $B(x,u)$ from the steady-state monomials and the conservation laws (a Jacobian-determinant-type polynomial), whose terms at $u = 0$ all share one sign; a term of the opposite sign whose $u$-exponent is supported on a set of intermediates certifies that adding exactly those intermediates yields multistationarity. Computing these terms for all $I$ with $n \le 8$ suggested the pattern, which is then proved for all $n$ using the toric (Gale-dual) description of the steady states.

## Sources

- Alicia Dickenstein, Magalí Giaroli, Mercedes Pérez Millán, Rick Rischter, "Multistationarity questions in reduced vs extended biochemical networks", *Journal of Mathematical Biology* 89(2) (2024), 18, Definitions 3.6, 3.7 and 5.1, Proposition 3.8, Theorems 3.20 and 5.3, <https://doi.org/10.1007/s00285-024-02115-7> (preprint arXiv:2310.02455).
