# Priceable committee in an approval election

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$. Priceability is defined for every set $W \subseteq C$, of any size and without reference to $k$, so it also applies to outputs with fewer than $k$ members such as those of the Method of Equal Shares. A price system is a pair $(p, \{\pi_i\}_{i \in N})$ with $p > 0$ and payment functions $\pi_i : C \to [0, \infty)$ such that $\sum_{c} \pi_i(c) \le 1$ for each voter, $\pi_i(c) = 0$ whenever $c \notin A_i$, $\sum_{i} \pi_i(c) = p$ for $c \in W$, $\sum_{i} \pi_i(c) = 0$ for $c \notin W$, and for every $c \notin W$,

$$
\sum_{i \in N_c} \Bigl(1 - \sum_{c' \in C} \pi_i(c')\Bigr) \le p .
$$

A set $W \subseteq C$ is priceable if some price system supports it in this sense.

## Depends on

- [Approval-based committee elections](../../computational-social-choice/approval-based-committee-elections.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
