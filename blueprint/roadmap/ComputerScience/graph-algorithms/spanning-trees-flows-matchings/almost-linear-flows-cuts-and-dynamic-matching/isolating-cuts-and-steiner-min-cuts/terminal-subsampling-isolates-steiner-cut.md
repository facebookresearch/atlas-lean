# Terminal subsampling isolates one side of a Steiner minimum cut

Let $S^{*}$ be an $R$-Steiner minimum cut of $G$, chosen (after possibly complementing) so that $k = |S^{*} \cap R| \le |R \setminus S^{*}|$, and let $i = \lfloor \log_2(|R|/k) \rfloor \ge 1$. Let $R' \subseteq R$ be a uniformly random subset of exactly $2^i$ terminals. Then $|R' \cap S^{*}| = 1$ with probability $\Omega(1)$ (a constant independent of $G$, $R$ and $k$). On this event $R' \setminus S^{*} \ne \emptyset$, since $|R'| = 2^i \ge 2$, and if $v$ is the unique terminal of $R' \cap S^{*}$ then the minimum $v$-isolating cut with respect to $R'$ has value exactly $\lambda_R(G)$; in particular

$$
\min_{u \in R'} \min \{\, w(\partial S) : S \cap R' = \{u\} \,\} = \lambda_R(G).
$$

## Proof sketch

Write $N = |R|$ and $s = 2^i$, so $N/(2k) < s \le N/k$. If $k = 1$, the probability is $s/N > 1/2$. Otherwise the number of terminals of $S^{*}$ in $R'$ is hypergeometric, and $\Pr[|R' \cap S^{*}| = 1] = \frac{ks}{N} \prod_{j=1}^{k-1}\bigl(1 - \frac{s-1}{N-j}\bigr)$; since $s \le N/k$, each factor is at least $1 - 1/k$, so the probability is at least $\tfrac12 (1 - 1/k)^{k-1} \ge 1/(2e)$. On the event, $S^{*}$ is $v$-isolating for $R'$, so the minimum isolating value is at most $\lambda_R(G)$; conversely every $R'$-isolating cut separates two terminals of $R$ and is therefore an $R$-Steiner cut of value at least $\lambda_R(G)$.

## Depends on

- [Minimum isolating cuts of a terminal set](minimum-isolating-cuts.md)
- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008, Section 3 (proof of Theorem 1.2).
