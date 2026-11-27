# Critical truth assignments for the pigeonhole principle

For sets $P$ of pigeons and $H$ of holes with $|P| = |H| + 1$, an assignment to the variables $p_{i,j}$ ($i \in P$, $j \in H$) is *critical* if it encodes a perfect matching between $P \setminus \{i_0\}$ and $H$ for one pigeon $i_0$, the omitted pigeon, and sets all other variables false. A critical assignment satisfies every hole clause and every pigeon clause except the one of $i_0$. For a clause $C$, the *monotonization* replaces each negative literal $\neg p_{i,j}$ by $\bigvee_{i' \ne i} p_{i',j}$; on critical assignments $C$ and its monotonization agree.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](pigeonhole-formulas.md)

## Sources

- P. Beame and T. Pitassi, "Simplified and Improved Resolution Lower Bounds", Proceedings of the 37th IEEE Symposium on Foundations of Computer Science (FOCS), 1996: Section 3.
- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 297–308, 1985.
