# Order cones of fitness rankings and adjacent-transposition paths

For a partial order $P$ on a set $G$ of $k$ genotypes, the **order cone** $C_P \subset \mathbb{R}^G$ is the set of fitness vectors whose coordinates satisfy $P$; it is a convex polyhedral cone. A genetic interaction $f$ (an integer contrast in the fitnesses) defines the open half-space $H_{f,+} = \{f > 0\}$.

**Theorem (geometric form).** $C_P \subset H_{f,+}$ if and only if $P$ admits the pairing of the matching criterion, i.e. $P$ implies positive $f$-interaction. In particular, if $A$ and $B$ are linear orders with $C_A, C_B \subset H_{f,+}$, the cone of their intersection order $A \cap B$ lies in $H_{f,+}$ exactly when $A \cap B$ satisfies the pairing condition.

**Theorem (connectivity).** Let $U \subset \mathbb{R}^k$ be open and path connected, meeting the cones $C_A$ and $C_B$ of linear orders $A$ and $B$. Then there are linear orders $A = L_1, \dots, L_n = B$ with $L_{i+1}$ obtained from $L_i$ by one adjacent transposition and $U \cap C_{L_i} \ne \emptyset$ for every $i$.

**Corollary.** If two linear orders $A$ and $B$ both imply positive $f$-interaction, they are joined by a chain of adjacent transpositions none of whose members implies negative $f$-interaction.

## Depends on

- [Matching criterion for genetic interactions implied by a partial fitness order](matching-criterion-for-interactions-implied-by-a-partial-order.md)

## Expansion

The cones of the $k!$ linear orders tile $\mathbb{R}^k$ (up to boundaries), and two of them share a $(k-1)$-dimensional face exactly when the orders differ by one adjacent transposition. A path in $U$ from $C_A$ to $C_B$ can be perturbed to cross only codimension-one faces, giving the chain. Applied to $U = H_{f,+}$, which misses every cone inside $\{f < 0\}$, it yields the corollary. The result supports Markov chain samplers that move between fitness rankings by adjacent swaps when quantifying uncertainty about interactions.

## Sources

- C. Lienkaemper, L. Lamberti, J. Drain, N. Beerenwinkel, A. Gavryushkin, *The geometry of partial fitness orders and an efficient method for detecting genetic interactions*, J. Math. Biol. 77 (2018), 951–970 (Section 5, Definitions 3–4, Theorems 5–6, Corollaries 1–2). <https://doi.org/10.1007/s00285-018-1237-7> (PMCID: PMC6153669)
