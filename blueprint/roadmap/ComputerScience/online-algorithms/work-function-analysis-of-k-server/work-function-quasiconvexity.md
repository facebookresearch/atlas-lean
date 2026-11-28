# Quasiconvexity of work functions

Every work function $w$ of a $k$-server instance is *quasiconvex*: for any two configurations $A, B$ there is a bijection $h : A \to B$ such that for every partition $A = X \sqcup Y$, $w(A) + w(B) \ge w\big(X \cup h(Y)\big) + w\big(h(X) \cup Y\big)$.

## Proof sketch

Induct on the number of requests. The initial work function $w_0(X) = d(A_0, X)$ is a matching distance and satisfies the inequality with $h$ the optimal matching. For the update $w_t(X) = \min_{Z \ni r_t}\big(w_{t-1}(Z) + d(Z, X)\big)$, take minimizers $Z_A, Z_B$ for $A, B$, apply the induction hypothesis to $Z_A, Z_B$ with its bijection, compose with the optimal matchings between $Z_A$ and $A$ and between $Z_B$ and $B$, and use the triangle inequality to recombine the parts.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
