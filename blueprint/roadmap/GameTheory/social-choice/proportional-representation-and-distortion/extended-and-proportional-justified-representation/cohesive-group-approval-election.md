# Cohesive group of voters in an approval election

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. For an integer $\ell$ with $1 \le \ell \le k$, a set of voters $N' \subseteq N$ is $\ell$-cohesive if

$$
\lvert N' \rvert \ge \ell \cdot \frac{n}{k} \qquad \text{and} \qquad \Bigl\lvert \bigcap_{i \in N'} A_i \Bigr\rvert \ge \ell .
$$

A $1$-cohesive group is a group of at least $n/k$ voters sharing an approved candidate, which is the hypothesis of justified representation.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman, T. Walsh, "Justified Representation in Approval-Based Committee Voting", Social Choice and Welfare 48(2) (2017), arXiv:1407.8269.
