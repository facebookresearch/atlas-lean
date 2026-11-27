# Every QBF lower bound comes from circuits, resolution, or genuine QBF hardness

For QBF proof systems with strategy extraction, any super-polynomial lower bound on $\forall\exists$ QBFs with CNF matrix arises from a circuit lower bound for witnessing strategies, from a resolution lower bound for the witnessed formula, or from genuine QBF hardness.

A QBF proof system $P$ has the **strategy extraction property** (by circuits of a class $\mathcal{C}$) if from every $P$-proof $\pi$ of $\psi = \forall x_1 \exists y_1 \dots \forall x_n \exists y_n .\, \phi$ one obtains $|\pi|^{O(1)}$-size circuits $C_i \in \mathcal{C}$ with $\bigwedge_{i=1}^n (y_i \leftrightarrow C_i(x_1, \dots, x_i, y_1, \dots, y_{i-1})) \to \phi$ valid.

**Theorem.** Let $P$ be a refutational QBF proof system operating on clauses of prenex QBFs with a resolution rule on both existential and universal variables, admitting strategy extraction by $\mathcal{C}$ circuits. If the QBFs $\psi_n = \forall x_1 \exists y_1 \dots \forall x_n \exists y_n .\, \phi_n$, with $\phi_n$ a propositional CNF, have no polynomial-size $P$-proofs, then one of the following holds:

1. **Circuit lower bound:** the existential variables of $\psi_n$ are not witnessable by $\mathcal{C}$ circuits.
2. **Resolution lower bound:** item 1 fails, but for all $\mathcal{C}$ circuits witnessing $\psi_n$ the witnessed formulas $\bigwedge_i (y_i \leftrightarrow C_i) \land \neg \phi_n$ require super-polynomial resolution refutations.
3. **Genuine QBF hardness:** some witnessing circuits $C_i \in \mathcal{C}$ give witnessed formulas with polynomial-size resolution refutations, but for all such circuits it is hard to derive $\bigwedge_i C_i(x_1, \dots, x_i, y_1, \dots, y_{i-1}) = y_i$ from $\neg \phi_n$ in $P$.

**Example.** The formulas $\mathrm{KBKF}'_n$, obtained from the Kleine Büning-Karpinski-Flögel formulas by adding universal variables $z_k$ next to $x_k$ and the literal $z_k$ or $\overline{z}_k$ to each clause containing $x_k$ or $\overline{x}_k$, require exponential QU-resolution proofs, and they are hard for QU-resolution because of genuine QBF hardness (item 3).

## Expansion

For strong systems the third case cannot occur: for $\mathcal{C}$-Frege plus universal reduction with $\mathcal{C} \in \{\mathrm{NC}^1, \mathrm{P/poly}\}$, formalized strategy extraction gives, from a refutation $\pi$, circuits $C_i \in \mathcal{C}$ and in time $|\pi|^{O(1)}$ a tree-like resolution refutation of the witnessed formula, the extension variables of the Frege proof being absorbed into the circuits $C_i$. So lower bounds for extended Frege plus universal reduction are circuit lower bounds or extended Frege lower bounds. For weaker systems such as QU-resolution, $\mathrm{KBKF}'_n$ has a short winning strategy $x_k = z_k = y'_k$ whose witnessed formula has a linear-size resolution refutation, yet the system cannot derive the witnessing equations efficiently.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, L. Hinde, J. Pich, "Reasons for hardness in QBF proof systems", *ACM Transactions on Computation Theory*, 2020, doi:10.1145/3378665 (conference version FSTTCS 2017, LIPIcs 93, doi:10.4230/LIPIcs.FSTTCS.2017.14, whose numbering is cited) (Section 3: the strategy extraction property, Theorem 1, Theorem 2, Definition 3 and Theorem 4).
