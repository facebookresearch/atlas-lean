# Success probability of one Schöning trial

Let $k \ge 3$ and let $\varphi$ be a satisfiable CNF formula on $n \ge 1$ variables with clauses of at most $k$ literals. There is a polynomial $q_k$, depending only on $k$, such that one Schöning trial succeeds with probability at least

$$
\left(\frac{k}{2(k-1)}\right)^{n} \Big/ \, q_k(n).
$$

For $k = 3$ the probability is at least $\frac{c}{\sqrt n}\left(\frac34\right)^n$ with $c = \sqrt{3/(64\pi)}$.

## Proof sketch

Fix a satisfying assignment $\sigma^*$. Each flip in a falsified clause moves toward $\sigma^*$ with probability at least $1/k$. Bound the probability of reaching distance $0$ from initial distance $j$ within $3j$ steps by a ballot-type count of walks, then average over the binomial distribution of $j$. Carrying the constants through the count gives the explicit bound

$$
p_{k,n} \;=\; \frac{1}{3n+1}\left(\frac{k}{2(k-1)}\right)^{n}\left(\frac{k-1}{k}\right)^{k-3},
$$

which for $k = 3$ is $\frac{1}{3n+1}(3/4)^n$.

## Depends on

- [Schöning's random-walk trial](schoening-random-walk-trial.md)

## Sources

- U. Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th IEEE Symposium on Foundations of Computer Science (FOCS), 1999.
- H. Röglin, "Probabilistic Analysis of Algorithms", University of Bonn lecture notes, Summer 2016, Ch. 4, pp. 69-71: (4.3), the success probability $q \ge \frac{c}{\sqrt n}(3/4)^n$ of one iteration of Improved-3-SAT with $c = \sqrt3/\sqrt{64\pi}$, and Theorem 4.6. <https://nerva.cs.uni-bonn.de/lib/exe/fetch.php/lehre/ss16/vl-rapa/rapa-lecture13.pdf>
- L. Rohwedder, DM898 (University of Southern Denmark, 2025), Lecture 18 "Randomized Methods II: Walk-SAT": for $k$-SAT, $N = 3n$ and $O((2 - 2/k)^n)$ iterations succeed with probability $0.99$, and running time $(2 - 2/k)^n \cdot n^{O(1)}$; for 3-SAT, one iteration succeeds with probability $\Omega(\frac{1}{\sqrt n}(3/4)^n)$. <https://larsrohwedder.com/teaching/dm898-25/lecture18.pdf>
