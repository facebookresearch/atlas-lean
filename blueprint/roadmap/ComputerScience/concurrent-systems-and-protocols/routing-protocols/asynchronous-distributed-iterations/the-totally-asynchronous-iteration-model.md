# The totally asynchronous iteration model

Let $f$ map a set $X$ of vectors $x = (x_i)_{i \in I}$, $x_i \in [-\infty, \infty]$, into itself, with fixed points $x^* = f(x^*)$. The index set $I$ is partitioned into disjoint sets $I_1, \dots, I_n$, one per node: node $j$ is responsible for the coordinates $x_i$, $i \in I_j$. Node $j$ keeps a buffer $B_{jj}$ with its own estimate of those coordinates and, for each $m \ne j$, a buffer $B_{jm}$ with the latest estimate received from $m$; $x^t(j)$ is the vector of all buffer contents of node $j$ at time $t$. Nodes alternate, in uninterrupted time intervals, between computing, transmitting and idling:

1. at the end of a computation interval $[t_1, t_2]$ of node $j$, $x^{t_2}_i(j) = f_i(x^{t_1}(j))$ for $i \in I_j$;
2. at the end of a transmission interval $[t_1, t_2]$ from $m$ to $j$, buffer $B_{jm}$ receives the contents of $B_{mm}$ at time $t_1$;
3. no buffer changes otherwise.

Nothing is assumed about the lengths, timing or order of these intervals except that no node drops out (*Assumption A*): for every node $j$ and time $t$ there is $t' > t$ such that $[t, t']$ contains a computation interval of $j$ and a transmission interval from $j$ to every other node. The question is whether $\lim_{t \to \infty} x^t_i(j) = x^*_i$ for all $i$ and $j$.

## Sources

- D. P. Bertsekas, "Distributed asynchronous computation of fixed points", *Mathematical Programming* 27:107–120, 1983; <https://web.mit.edu/dimitrib/OldFiles/www/Distr_Comp_Fixed.pdf>, Section 2 (the algorithmic model, update rules (7)–(8) and Assumption A).
