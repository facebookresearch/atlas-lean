# Fair division of mixed goods and chores

An instance of mixed fair division has a finite set $N$ of $n$ agents and a finite set $M$ of items, and each agent $i$ has an additive utility $u_i(S) = \sum_{o \in S} u_i(o)$ with $u_i(o) \in \mathbb{R}$ of arbitrary sign. Item $o$ is a good for $i$ if $u_i(o) > 0$ and a chore for $i$ if $u_i(o) < 0$. A complete allocation $X$ is EF1 if for all $i, j$ with $X_i \cup X_j \ne \emptyset$ there is an item $o \in X_i \cup X_j$ with $u_i(X_i \setminus \{o\}) \ge u_i(X_j \setminus \{o\})$; that is, envy is eliminated by removing one good from the envied bundle or one chore from the envious agent's bundle. It is PROP1 if for every $i$ either $u_i(X_i) \ge u_i(M)/n$ or there is $o \in M$ with $u_i(X_i \cup \{o\}) \ge u_i(M)/n$ ($o \notin X_i$ a good) or $u_i(X_i \setminus \{o\}) \ge u_i(M)/n$ ($o \in X_i$ a chore).

## Depends on

- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)
- [Proportional allocation](../../../not-yet-classified/part-01/indivisible/is-proportional.md)

## Sources

- H. Aziz, I. Caragiannis, A. Igarashi, T. Walsh, "Fair allocation of indivisible goods and chores", IJCAI 2019; Autonomous Agents and Multi-Agent Systems 36 (2022).
- H. Aziz, H. Moulin, F. Sandomirskiy, "A polynomial-time algorithm for computing a Pareto optimal and almost proportional allocation", Operations Research Letters 48(5) (2020), arXiv:1909.00740.
