# Success probability of one Schöning trial

Let $k \ge 3$ and let $\varphi$ be a satisfiable CNF formula on $n$ variables with clauses of at most $k$ literals. One Schöning trial succeeds with probability at least

$$
p_{k,n} \;=\; \frac{1}{3n+1}\left(\frac{k}{2(k-1)}\right)^{n}\left(\frac{k-1}{k}\right)^{k-3}.
$$

For $k = 3$ this is $\frac{1}{3n+1}(3/4)^n$.

## Proof sketch

Fix a satisfying assignment $\sigma^*$. Each flip in a falsified clause moves toward $\sigma^*$ with probability at least $1/k$. Bound the probability of reaching distance $0$ from initial distance $j$ within $3j$ steps by a ballot-type count of walks, then average over the binomial distribution of $j$.

## Depends on

- [Schöning's random-walk trial](schoening-random-walk-trial.md)

## Sources

- U. Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th IEEE Symposium on Foundations of Computer Science (FOCS), 1999.
