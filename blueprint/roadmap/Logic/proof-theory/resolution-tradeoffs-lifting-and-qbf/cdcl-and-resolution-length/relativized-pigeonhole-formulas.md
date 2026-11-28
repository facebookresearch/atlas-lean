# Relativized pigeonhole principle formulas

The relativized pigeonhole formula with $k$ pigeons, $n$ resting places and $k-1$ holes claims that $k$ pigeons can be sent injectively to $n$ resting places and from the occupied ones injectively into $k-1$ holes; its 3-CNF version has narrow but long refutations.

Let $k \ge 2$ and $n \ge k$. The formula $\mathrm{RPHP}^k_{n,k-1}$ has variables $p_{u,v}$ ($u \in [k]$, $v \in [n]$) encoding a map $p : [k] \to [n]$, variables $q_{v,w}$ ($v \in [n]$, $w \in [k-1]$) encoding a map $q : [n] \to [k-1]$, and variables $r_v$ ($v \in [n]$) encoding a superset of the range of $p$. Its clauses are

$$
\begin{aligned}
& p_{u,1} \lor \dots \lor p_{u,n} && u \in [k], \\
& \overline{p}_{u,v} \lor \overline{p}_{u',v} && u \ne u' \in [k],\ v \in [n], \\
& \overline{p}_{u,v} \lor r_v && u \in [k],\ v \in [n], \\
& \overline{r}_v \lor q_{v,1} \lor \dots \lor q_{v,k-1} && v \in [n], \\
& \overline{r}_v \lor \overline{r}_{v'} \lor \overline{q}_{v,w} \lor \overline{q}_{v',w} && v \ne v' \in [n],\ w \in [k-1].
\end{aligned}
$$

The first two families say that $p$ maps $[k]$ injectively into $[n]$, the third records its range, and the last two force $q$ to be defined and injective on that range, which is impossible by the pigeonhole principle. The **3-CNF version** $F_{n,k}$ splits the clauses of the first family when $n \ge 4$ and those of the fourth family when $k \ge 4$ into chains with extension variables $y_{u,v}$ and $z_{v,w}$, keeps them unchanged when their width is at most $3$ (that is, $n \le 3$, respectively $k \le 3$), and splits the 4-clauses of the last family with extension variables $r_{v,v'}$. For $n \ge 4$ the first family is replaced by

$$
\begin{aligned}
& p_{u,1} \lor p_{u,2} \lor y_{u,2} && u \in [k], \\
& \overline{y}_{u,v} \lor p_{u,v+1} \lor y_{u,v+1} && u \in [k],\ v \in [2, n-3], \\
& \overline{y}_{u,n-2} \lor p_{u,n-1} \lor p_{u,n} && u \in [k],
\end{aligned}
$$

for $k \ge 4$ the fourth family is replaced by

$$
\begin{aligned}
& \overline{r}_v \lor q_{v,1} \lor z_{v,1} && v \in [n], \\
& \overline{z}_{v,w} \lor q_{v,w+1} \lor z_{v,w+1} && v \in [n],\ w \in [k-4], \\
& \overline{z}_{v,k-3} \lor q_{v,k-2} \lor q_{v,k-1} && v \in [n],
\end{aligned}
$$

and the remaining clauses are

$$
\begin{aligned}
& \overline{p}_{u,v} \lor \overline{p}_{u',v} && u \ne u' \in [k],\ v \in [n], \\
& \overline{p}_{u,v} \lor r_v && u \in [k],\ v \in [n], \\
& \overline{r}_v \lor \overline{r}_{v'} \lor r_{v,v'} && v \ne v' \in [n], \\
& \overline{r}_{v,v'} \lor \overline{q}_{v,w} \lor \overline{q}_{v',w} && v \ne v' \in [n],\ w \in [k-1].
\end{aligned}
$$

Each chain resolves back to the wide clause it replaces, so $F_{n,k}$ is unsatisfiable. The source splits only the wide clauses; the chains above need $n \ge 4$ and $k \ge 4$ to be well formed, since for smaller values they would use the variables $y_{u,1}$, $z_{v,0}$ or $q_{v,0}$, or leave two different extension variables unlinked.

It has $O(n^2)$ variables and $O(k n^2)$ clauses.

## Expansion

The formula is unsatisfiable because any assignment satisfying the first three families marks at least $k$ resting places with $r_v = 1$, and the last two families then give an injection of these $k$ places into $k - 1$ holes. Only $k$ out of $n$ resting places matter, which is what makes width $O(k)$ suffice while length must be $n^{\Omega(k)}$.

## Depends on

- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

None.

## Sources

- A. Atserias, M. Lauria, J. Nordström, "Narrow proofs may be maximally long", *ACM Transactions on Computational Logic* 17(3), 2016 (conference version CCC 2014), doi:10.1145/2898435, arXiv:1409.2731v1 (Section 3.1, the definition of the formula, clause families (3.1a)-(3.1e) of the wide encoding and the 3-CNF clauses (3.2a)-(3.2j)).
