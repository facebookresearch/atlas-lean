# Held–Karp dynamic program for the traveling salesman problem

Let $V$ be a finite set of $n \ge 2$ cities with a start city $s$ (for instance $V = \{1, \dots, n\}$ and $s = 1$), and let $d(i, j)$ be arbitrary costs with values in a linearly ordered additive commutative monoid $R$, such as $\mathbb{Z}$ or $\mathbb{R}$: they may be negative, and $d(i, j)$ need not equal $d(j, i)$. For a set $S$ of cities and a city $j$, let $C(S, j)$ be the [minimum](min-path-cost.md), in $R \cup \{\top\}$, of the costs $d(s, x_1) + d(x_1, x_2) + \dots + d(x_{k-1}, x_k)$ of the [paths](is-hamiltonian-path.md) $s, x_1, \dots, x_k$ that start at $s$, visit exactly the cities of $S$, each once, and end at $j$; it is $\top$ when there is no such path.

**Theorem.**

1. If $s \in S$ and $j \in S \setminus \{s\}$, such a path exists, and $C(S, j)$ is the least cost of such a path.
2. $C(\{s, j\}, j) = d(s, j)$ for every city $j \ne s$.
3. If $s \in S$, $j \in S \setminus \{s\}$ and $|S| \ge 3$, then

    $$C(S, j) = \min_{i \in S \setminus \{s, j\}} \bigl(C(S \setminus \{j\}, i) + d(i, j)\bigr).$$

4. The [optimal tour cost](optimal-tour-cost.md), the least cost $d(y_1, y_2) + \dots + d(y_{n-1}, y_n) + d(y_n, y_1)$ of a closed tour $y_1, \dots, y_n$ that visits every city exactly once, is $\min_{j \in V \setminus \{s\}} \bigl(C(V, j) + d(j, s)\bigr)$.
5. Given a list of the cities other than $s$, each listed once, the [Held–Karp algorithm](solve.md) fills a table $T(A, v)$, for the nonempty sets $A$ of cities other than $s$ and the cities $v \in A$, level by level in $|A|$: $T(\{v\}, v) = d(s, v)$, and $T(A, v) = \min_{u \in A \setminus \{v\}} \bigl(T(A \setminus \{v\}, u) + d(u, v)\bigr)$ when $|A| \ge 2$. It returns $\min_{v \in V \setminus \{s\}} \bigl(T(V \setminus \{s\}, v) + d(v, s)\bigr)$, which is the optimal tour cost, after at most $n^2 2^n$ steps, and it stores at most $n 2^n$ table entries. A step is a base entry, a candidate $u$ examined in a minimum (a table read, an addition and a comparison) or a candidate $v$ examined in the final minimum; set operations, table writes and the enumeration of the sets are not counted separately. With sets stored as bit masks, as in Eppstein's notes, each of them takes constant time when $n$ is at most the machine word size.

**Proof.**

1. The path that starts at $s$, visits the cities of $S \setminus \{s, j\}$ in any order and ends at $j$ is such a path, and there are finitely many.
2. The only path from $s$ to $j$ through $\{s, j\}$ is $s, j$, of cost $d(s, j)$.
3. As $|S| \ge 3$, a path from $s$ to $j$ through $S$ has a city $i \in S \setminus \{s, j\}$ just before $j$, and removing $j$ leaves a path from $s$ to $i$ through $S \setminus \{j\}$ whose cost is smaller by $d(i, j)$. Conversely, appending $j$ to a path from $s$ to such an $i$ through $S \setminus \{j\}$ gives a path from $s$ to $j$ through $S$. Since adding $d(i, j)$ preserves the order, minimising first over the paths ending at $i$ and then over $i$ gives the recurrence.
4. Rotating a closed tour does not change its cost, so every tour may be taken to start at $s$. Such a tour is a path from $s$ through $V$ to a city $j$, which differs from $s$ as $n \ge 2$, followed by the return from $j$ to $s$, of cost $d(j, s)$.
5. By induction on $|A|$, using parts 2 and 3, the algorithm stores $T(A, v) = C(A \cup \{s\}, v)$, so part 4 shows that it returns the optimal tour cost. With $m = n - 1$, there are $\binom{m}{k}$ sets $A$ of size $k$, each with $k$ entries, and an entry costs $1$ step if $k = 1$ and $k - 1$ steps otherwise. So there are $m + \sum_{k=1}^{m} \binom{m}{k} k \max(1, k - 1) \le m + m^2 2^m \le n^2 2^n$ steps and $\sum_{k=1}^{m} \binom{m}{k} k \le m 2^m \le n 2^n$ entries.

## Sources

- D. Eppstein, "Lecture 5b: Exact TSP algorithm", lecture notes for CS 163 & CS 265: Graph Algorithms, week 5, University of California, Irvine, winter quarter 2026, <https://ics.uci.edu/~eppstein/163/lecture5b.pdf>: the table of shortest paths from $s$ to $v$ covering a set $A$ of vertices other than $s$, filled over the sets $A$ by the minimum over the second-to-last vertex, the final minimum that returns to $s$, and the $O(n^2 2^n)$ time bound. Here $C$ is indexed by $S = A \cup \{s\}$, and the table $T$ of part 5 keeps the indexing by $A$; the explicit step bound and the count of table entries are written out here.
- M. Held and R. M. Karp, "A dynamic programming approach to sequencing problems", *Journal of the Society for Industrial and Applied Mathematics* 10(1):196–210, 1962, doi:10.1137/0110015
- R. Bellman, "Dynamic programming treatment of the travelling salesman problem", *Journal of the ACM* 9(1):61–63, 1962, doi:10.1145/321105.321111
