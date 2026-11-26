# Leximax Phragmén satisfies PJR and sequential Phragmén is committee monotone

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. In Phragmén's load distribution framework, each elected candidate carries one unit of load distributed among voters approving it, and the leximax-Phragmén rule selects a committee together with a load distribution minimizing the vector of voter loads sorted in non-increasing order lexicographically. Leximax-Phragmén satisfies PJR. Sequential Phragmén is committee monotone: the committee it selects for size $k$ is contained in the committee it selects for size $k + 1$ (with consistent tie-breaking), whereas no committee-monotone rule satisfies EJR for all committee sizes.

## Proof sketch

For PJR, an underrepresented $\ell$-cohesive group would allow shifting load from the most loaded voters to a commonly approved unelected candidate, lowering the maximum load and contradicting leximax optimality. Committee monotonicity of sequential Phragmén is immediate from its sequential definition, which does not depend on $k$. The impossibility for EJR uses a profile where EJR for size $k$ forces a committee incompatible with EJR at size $k+1$ in any nested way.

## Depends on

- [Proportional justified representation](proportional-justified-representation.md)
- [Sequential Phragmén satisfies proportional justified representation](sequential-phragmen-satisfies-pjr.md)

## Proof depends on

- [Sequential Phragmén satisfies proportional justified representation](sequential-phragmen-satisfies-pjr.md)

## Sources

- M. Brill, R. Freeman, S. Janson, M. Lackner, "Phragmén's Voting Methods and Justified Representation", AAAI 2017; Mathematical Programming 203 (2024).
- M. Lackner, P. Skowron, "Multi-Winner Voting with Approval Preferences", SpringerBriefs in Intelligent Systems (2023), arXiv:2007.01795.
