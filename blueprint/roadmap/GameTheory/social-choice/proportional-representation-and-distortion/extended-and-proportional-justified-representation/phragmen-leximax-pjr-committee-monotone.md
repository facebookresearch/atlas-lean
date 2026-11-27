# Leximax Phragmén satisfies PJR and sequential Phragmén is committee monotone

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. As in Brill, Freeman, Janson and Lackner, assume that every candidate is approved by at least one voter, $N_c = \{ i : c \in A_i \} \ne \emptyset$ for every $c \in C$; an elected candidate approved by nobody could not carry its unit of load. In Phragmén's load distribution framework, each elected candidate carries one unit of load distributed among voters approving it, and the leximax-Phragmén rule selects a committee together with a load distribution minimizing the vector of voter loads sorted in non-increasing order lexicographically. Leximax-Phragmén satisfies PJR. Sequential Phragmén, which starts from zero voter loads and in each round adds an unchosen candidate $c$ minimizing $s_c = (1 + \sum_{i \in N_c} \ell_i)/\lvert N_c \rvert$ and sets $\ell_i := s_c$ for every $i \in N_c$, is committee monotone: the committee it selects for size $k$ is contained in the committee it selects for size $k + 1$ (with consistent tie-breaking). Sequential Phragmén also satisfies PJR, which makes it one of few committee monotone rules with this property, and leximax-Phragmén fails EJR.

## Proof sketch

For PJR, suppose an $\ell$-cohesive group $N'$ has fewer than $\ell$ members of $W$ approved by its voters. Their total load is at most $\ell - 1$, so their average load is at most $k/n - 1/\lvert N' \rvert$, and some voter outside $N'$ carries load above $k/n$. Replacing a candidate whose load reaches that voter by a commonly approved unelected candidate of $N'$, whose unit of load is spread over $N'$, lowers the load vector in the leximax order, contradicting optimality. Committee monotonicity of sequential Phragmén is immediate from its sequential definition, which does not depend on $k$. Leximax-Phragmén satisfies perfect representation whenever a perfectly representing committee exists, and perfect representation is incompatible with EJR.

## Depends on

- [Proportional justified representation](proportional-justified-representation.md)
- [Extended justified representation](extended-justified-representation.md)

## Sources

- M. Brill, R. Freeman, S. Janson, M. Lackner, "Phragmén's Voting Methods and Justified Representation", AAAI 2017; Mathematical Programming 203 (2024).
- M. Lackner, P. Skowron, "Multi-Winner Voting with Approval Preferences", SpringerBriefs in Intelligent Systems (2023), arXiv:2007.01795.
