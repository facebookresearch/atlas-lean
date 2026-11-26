# Terminal subsampling isolates one side of a Steiner minimum cut

Let $S^{*}$ be an $R$-Steiner minimum cut of $G$, chosen (after possibly complementing) so that $k = |S^{*} \cap R| \le |R \setminus S^{*}|$, and let $j \ge 0$ be the integer with $2^{j-1} < k \le 2^j$. Let $R' \subseteq R$ contain each terminal independently with probability $p = 2^{-j}$. Then with probability at least $1/15$ the sample satisfies $|R' \cap S^{*}| = 1$ and $R' \setminus S^{*} \ne \emptyset$. On this event $|R'| \ge 2$, and if $v$ is the unique terminal of $R' \cap S^{*}$ then the minimum $v$-isolating cut with respect to $R'$ has value exactly $\lambda_R(G)$; in particular

$$
\min_{u \in R'} \min \{\, w(\partial S) : S \cap R' = \{u\} \,\} = \lambda_R(G).
$$

## Proof sketch

If $k = 1$ then $p = 1$ and the event holds surely. Otherwise $p \in [1/(2k), 1/k]$, so $\Pr[|R' \cap S^{*}| = 1] = kp(1-p)^{k-1} \ge \tfrac12 (1 - 1/k)^{k-1} \ge 1/(2e)$, while $\Pr[R' \setminus S^{*} \ne \emptyset] \ge 1 - (1 - 1/(2k))^k \ge 1 - e^{-1/2}$, and the two events are independent, giving probability at least $(1 - e^{-1/2})/(2e) > 1/15$. On the event, $S^{*}$ is $v$-isolating for $R'$, so the minimum isolating value is at most $\lambda_R(G)$; conversely every $R'$-isolating cut separates two terminals of $R$ and is therefore an $R$-Steiner cut of value at least $\lambda_R(G)$.

## Depends on

- [Minimum isolating cuts of a terminal set](minimum-isolating-cuts.md)
- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
