# Online cost of the work function algorithm via extended costs

For every $k$-server instance and every $T$, the total cost of the work function algorithm on $r_1, \dots, r_T$ is at most $\sum_{t=1}^{T} \mathrm{ext}_t - \mathrm{OPT}_T$, where $\mathrm{OPT}_T = \min_X w_T(X)$ is the offline optimum.

## Proof sketch

Since $A_t \ni r_t$, the work function satisfies $w_t(A_t) = w_{t-1}(A_t)$, and by its Lipschitz form $w_t(Y) = \min_{X \ni r_t}\big(w_t(X) + d(X, Y)\big)$ together with the choice rule of the algorithm, $w_t(A_{t-1}) = w_t(A_t) + d(A_{t-1}, A_t)$. Hence the move at time $t$ costs $w_t(A_{t-1}) - w_{t-1}(A_t) = \big(w_t(A_{t-1}) - w_{t-1}(A_{t-1})\big) + \big(w_{t-1}(A_{t-1}) - w_t(A_t)\big)$. The second brackets telescope to $w_0(A_0) - w_T(A_T) \le -\mathrm{OPT}_T$, since $w_0(A_0) = 0$ for the initial configuration $A_0$ and $w_T(A_T) \ge \min_X w_T(X)$, and each first bracket is at most $\mathrm{ext}_t$.

## Depends on

- [Extended cost of a request](extended-cost.md)
- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009), Lemma 2 and equation (7).
