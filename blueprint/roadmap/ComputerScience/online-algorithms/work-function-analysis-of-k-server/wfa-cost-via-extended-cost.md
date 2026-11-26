# Online cost of the work function algorithm via extended costs

For every $k$-server instance and every $T$, the total cost of the work function algorithm on $r_1, \dots, r_T$ is at most $\sum_{t=1}^{T} \mathrm{ext}_t - \mathrm{OPT}_T + c_0$, where $\mathrm{OPT}_T = \min_X w_T(X)$ is the offline optimum and $c_0$ depends only on the initial configuration and the diameter of the points involved.

## Proof sketch

Since $A_t \ni r_t$, the work function satisfies $w_t(A_t) = w_{t-1}(A_t)$, and by its Lipschitz form $w_t(Y) = \min_{X \ni r_t}\big(w_t(X) + d(X, Y)\big)$ together with the choice rule of the algorithm, $w_t(A_{t-1}) = w_t(A_t) + d(A_{t-1}, A_t)$. Hence the move at time $t$ costs $w_t(A_{t-1}) - w_{t-1}(A_t) = \big(w_t(A_{t-1}) - w_{t-1}(A_{t-1})\big) + \big(w_{t-1}(A_{t-1}) - w_t(A_t)\big)$. The second brackets telescope to $w_0(A_0) - w_T(A_T) \le -\mathrm{OPT}_T + c_0$, and each first bracket is at most $\mathrm{ext}_t$.

## Depends on

- [Extended cost of a request](extended-cost.md)

## Proof depends on

- [Extended cost of a request](extended-cost.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009).
