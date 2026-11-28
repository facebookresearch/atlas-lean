# Maximum Nash welfare gives a tight Theta(1/sqrt(n)) maximin share guarantee

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Let $\mu_i$ denote the maximin share of agent $i$ for $n$ agents. Every maximum Nash welfare allocation $X$ satisfies

$$
v_i(X_i) \ge \frac{2}{1 + \sqrt{4n - 3}}\; \mu_i \quad \text{for every agent } i,
$$

and the ratio is tight: for every $n$ and every $\varepsilon > 0$ there is an instance with $n$ agents having additive valuations in which no maximum Nash welfare allocation gives every agent $i$ at least $\left(\frac{2}{1 + \sqrt{4n - 3}} + \varepsilon\right)\mu_i$; hence maximum Nash welfare is not $c$-MMS for any constant $c > 0$ independent of $n$.

## Proof sketch

Assume first that every agent has positive value, fix $i$, and for each $j \ne i$ let $g^*_j$ be the good of $X_j$ most valuable to $i$. EF1 gives $v_i(X_j \setminus \{g^*_j\}) \le v_i(X_i)$, and comparing the Nash product with the allocations obtained by moving $g^*_j$ to $i$, and by moving all of $X_j \setminus \{g^*_j\}$ to $i$, gives $v_i(X_j \setminus \{g^*_j\}) \le v_i(X_i)^2 / v_i(g^*_j)$. A counting argument over the $n$ parts of $i$'s maximin partition, separating the parts that contain one of the goods $g^*_j$, then yields a quadratic inequality in $\mu_i / v_i(X_i)$ whose root is $(1 + \sqrt{4n-3})/2$. Instances with zero Nash welfare are handled separately. The matching family places one agent against $n - 1$ agents with concentrated valuations.

## Depends on

- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)
- [Maximin share](../../../not-yet-classified/part-01/indivisible/maximin-share.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)
- [Maximum Nash welfare implies EF1](../../../not-yet-classified/part-01/max-nash-welfare-ef1/is-ef1-of-is-max-nash-welfare.md)

## Sources

- I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The Unreasonable Fairness of Maximum Nash Welfare", ACM Transactions on Economics and Computation 7(3) (2019); EC 2016, Theorem 4.1.
