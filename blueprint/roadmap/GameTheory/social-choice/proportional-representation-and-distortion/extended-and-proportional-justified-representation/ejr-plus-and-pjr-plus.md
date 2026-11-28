# EJR+ and PJR+ proportionality axioms

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. For a candidate $c$ write $N_c = \{ i \in N : c \in A_i \}$. A committee $W$ satisfies EJR+ if there is no candidate $c \in C \setminus W$, integer $\ell \in \{1, \dots, k\}$ and group $N' \subseteq N_c$ with $\lvert N'\rvert \ge \ell n / k$ such that $\lvert A_i \cap W \rvert < \ell$ for all $i \in N'$. It satisfies PJR+ if there is no $c \in C \setminus W$, $\ell$ and $N' \subseteq N_c$ with $\lvert N'\rvert \ge \ell n/k$ and $\bigl\lvert W \cap \bigcup_{i \in N'} A_i \bigr\rvert < \ell$.

## Depends on

- [Extended justified representation](extended-justified-representation.md)
- [Proportional justified representation](proportional-justified-representation.md)

## Sources

- M. Brill, J. Peters, "Robust and Verifiable Proportionality Axioms for Multiwinner Voting", EC 2023, arXiv:2302.01989.
