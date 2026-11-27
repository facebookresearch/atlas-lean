# Stabbing planes refute Tseitin formulas in quasi-polynomial size

Let $H = (V, E)$ be a connected graph with $n$ vertices and maximum degree $\Delta$, and let $\ell : V \to \{0,1\}$ be a charge function of odd total weight. The **Tseitin formula** $\mathrm{Tseitin}(H, \ell)$ has one variable $x_e$ per edge and, for every vertex $v$, the parity constraint $\sum_{e \ni v} x_e \equiv \ell(v) \pmod 2$, written as the at most $2^{\deg(v) - 1}$ clauses of width $\deg(v)$ that rule out the assignments to the edges at $v$ violating it. Summing all vertex constraints counts each edge twice but the charges once, so the formula is unsatisfiable. (This is the graph parity formula, not the Tseitin transformation of a Boolean formula into a CNF with gate variables.) $\mathrm{Tseitin}(H, \ell)$ has stabbing planes refutations of size $2^{O(\log^2 n) + \Delta}$ and depth $\Delta \cdot \log^2 n$.

## Proof sketch

For $U \subseteq V$ let $\mathrm{Cut}(U)$ be the edges with exactly one endpoint in $U$. The refutation maintains a set $U$ of vertices, initially $V$, together with queried inequalities that fix $\sum_{e \in \mathrm{Cut}(U)} x_e = k$ for some $k \not\equiv \sum_{v \in U} \ell(v) \pmod 2$; the constraints inside $U$ then contradict each other. Split $U$ into halves $U_1, U_2$. Threshold queries $\sum_{e \in \mathrm{Cut}(U_1, U_2)} x_e \ge \beta$ and $\sum_{e \in \mathrm{Cut}(U_1)} x_e \ge \gamma$ determine both values in two binary-search trees, and the identity $|\mathrm{Cut}(U_1)| + |\mathrm{Cut}(U_2)| = |\mathrm{Cut}(U)| + 2|\mathrm{Cut}(U_1, U_2)|$ then fixes the value $\delta$ on $\mathrm{Cut}(U_2)$, with $\delta + \gamma = k + 2\beta$. Leaves with $\delta$ out of range are refuted by the bounds $0 \le x_e \le 1$; otherwise one of $U_1, U_2$ has boundary value of the wrong parity, and the refutation recurses there. After $\log n$ halvings $U$ is a single vertex $v$ with its boundary sum fixed to a value of the wrong parity; querying $x_e \ge 1$ or $x_e \le 0$ for each of its at most $\Delta$ incident edges forces Boolean values, and each leaf then contradicts either the fixed sum or a clause of the constraint at $v$.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)

## Sources

- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), LIPIcs 94, Art. 10, doi:10.4230/LIPIcs.ITCS.2018.10, arXiv:1710.03219 (Theorem 6).
