# Sequential Phragmén satisfies proportional justified representation

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Sequential Phragmén builds a committee in $k$ rounds. All voters start with load $0$; in each round, for every candidate $c$ not yet chosen with approving voters $N_c = \{ i : c \in A_i \} \ne \emptyset$, let $s_c = \bigl(1 + \sum_{i \in N_c} \ell_i\bigr)/\lvert N_c \rvert$; a candidate with minimum $s_c$ is added and every $i \in N_c$ receives the new load $\ell_i := s_c$. The output always provides PJR, can be computed in polynomial time, and in general does not provide EJR.

## Proof sketch

Let $N'$ be $\ell$-cohesive and suppose fewer than $\ell$ members of $W$ are approved by voters of $N'$. Loads only increase and each selected candidate distributes one unit, so after the committee is complete the total load is $k$. As long as fewer than $\ell$ candidates approved by members of $N'$ have been chosen, the members of $N'$ carry total load less than $\ell$, so some common candidate $c$ of $N'$ has $s_c \le (1 + \text{load of } N')/\lvert N'\rvert < (1 + \ell)/\lvert N'\rvert$ bounds that stay at most $k/n$ up to the last needed round; meanwhile the minimum $s$ of every round never decreases and must exceed $k/n$ before $k$ candidates can be chosen without serving $N'$. Comparing the two bounds gives the contradiction; an explicit profile shows EJR can fail.

## Depends on

- [Proportional justified representation](proportional-justified-representation.md)

## Sources

- M. Brill, R. Freeman, S. Janson, M. Lackner, "Phragmén's Voting Methods and Justified Representation", AAAI 2017; Mathematical Programming 203 (2024).
