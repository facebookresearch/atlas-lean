# Sequential Phragmén satisfies proportional justified representation

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Assume, as Brill, Freeman, Janson and Lackner do, that every candidate is approved by at least one voter: $N_c = \{ i : c \in A_i \} \ne \emptyset$ for every $c \in C$. Without this the rule is not defined for all $k$ (with a single approved candidate and $k = 2$ no second candidate has a well-defined $s_c$). Sequential Phragmén builds a committee in $k$ rounds. All voters start with load $0$; in each round, for every candidate $c$ not yet chosen, let $s_c = \bigl(1 + \sum_{i \in N_c} \ell_i\bigr)/\lvert N_c \rvert$; a candidate with minimum $s_c$ is added and every $i \in N_c$ receives the new load $\ell_i := s_c$. The output always provides PJR, can be computed in polynomial time, and in general does not provide EJR.

## Proof sketch

Suppose a group $N'$ with $\lvert N' \rvert \ge \ell n/k$ and at least $\ell$ common candidates has fewer than $\ell$ members of $W$ approved by its voters; the argument works even for $\lvert N' \rvert > \ell n/(k+1)$. Each selected candidate adds exactly one unit to the total load, and voters of $N'$ gain load only from candidates they approve, so their total load is at most $\ell - 1$ throughout. In the last round some common candidate $c$ of $N'$ is unchosen, and since $N' \subseteq N_c$ the value $s_c$ is at most $(1 + \text{load of } N')/\lvert N' \rvert \le \ell/\lvert N' \rvert < (k+1)/n$. The maximum voter load after the last round equals the minimum $s$ of that round, so every voter ends with load below $(k+1)/n$; summing, the total load is less than $(\ell - 1) + (k + 1 - \ell) = k$, contradicting that it equals $k$. An explicit profile shows EJR can fail.

## Depends on

- [Proportional justified representation](proportional-justified-representation.md)
- [Extended justified representation](extended-justified-representation.md)

## Sources

- M. Brill, R. Freeman, S. Janson, M. Lackner, "Phragmén's Voting Methods and Justified Representation", AAAI 2017; Mathematical Programming 203 (2024).
