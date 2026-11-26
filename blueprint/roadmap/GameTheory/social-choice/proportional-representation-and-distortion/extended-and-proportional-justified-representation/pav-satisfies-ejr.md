# Proportional approval voting satisfies extended justified representation

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. Every committee maximizing the PAV score $\sum_{i} H(\lvert A_i \cap W \rvert)$ provides extended justified representation.

## Proof sketch

Suppose $W$ maximizes PAV but an $\ell$-cohesive group $N'$ has $\lvert A_i \cap W\rvert \le \ell - 1$ for all $i \in N'$. Some commonly approved candidate $c$ lies outside $W$, and adding it raises PAV by at least $\lvert N' \rvert / \ell \ge n/k$. In $W \cup \{c\}$, removing $w \in W$ costs voter $i$ the amount $1/(\lvert A_i \cap W\rvert + [c \in A_i])$ when $w \in A_i$; summing over $w \in W$, each voter of $N'$ contributes at most $(\ell - 1)/\ell$ and every other voter at most $1$, so the total is at most $n - \lvert N'\rvert/\ell \le n - n/k$. Hence some $w \in W$ has removal cost below $n/k$, and replacing $w$ by $c$ strictly increases the PAV score, a contradiction.

## Depends on

- [Extended justified representation](extended-justified-representation.md)
- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Proof depends on

- [Marginal contributions of a committee under proportional approval voting sum to the number of represented voters](pav-marginal-contribution-identity.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
