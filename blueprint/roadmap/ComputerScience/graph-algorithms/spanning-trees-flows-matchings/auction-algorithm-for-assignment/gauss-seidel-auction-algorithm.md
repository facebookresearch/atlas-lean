# Bertsekas's Gauss-Seidel auction algorithm

The **auction algorithm** with parameter $\varepsilon > 0$ starts with all persons unassigned and all prices $0$. While some person $i$ is unassigned, $i$ **bids**: it finds an object $j$ minimizing the reduced cost $v = c(i, j) + p(j)$ and the second smallest reduced cost $w$ over objects $k \ne j$ (with $w = v$ when $n = 1$), raises the price of $j$ to $w - c(i, j) + \varepsilon$ (an increase of $w - v + \varepsilon \ge \varepsilon$), assigns $j$ to $i$, and makes the previous owner of $j$ (if any) unassigned. The **scaled** version multiplies all costs by $n + 1$ and runs with $\varepsilon = 1$.

## Depends on

- [Epsilon-complementary slackness for the assignment problem](epsilon-complementary-slackness.md)

## Sources

- D. P. Bertsekas, "A Distributed Algorithm for the Assignment Problem", technical report, Laboratory for Information and Decision Systems, MIT, 1979.
- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
