# Minimum ranks under five-wise independence

Let $h$ be a random hash function from a finite set $X = \{x_0, x_1, \dots, x_n\}$ to the open interval $(0, 1)$ that is $5$-independent: each value $h(x)$ is uniform on $(0, 1)$, and the values at any five distinct points are independent. Then

$$
\Pr\Bigl[h(x_0) < \min_{1 \le i \le n} h(x_i)\Bigr] = O\Bigl(\frac{1}{n+1}\Bigr),
$$

so under $5$-independence every element is the strict minimum of the hash values with probability $O(1/|X|)$.

## Proof sketch

Condition on $h(x_0) = \alpha$; the remaining values are then $4$-wise independent. With $Z = \sum_{i=1}^n [h(x_i) \le \alpha]$, the event forces $Z = 0$, so it has conditional probability at most $\Pr[|Z - \mathbb{E}Z| \ge \mathbb{E}Z]$, which the fourth-moment inequality bounds by $O(1/(n\alpha)^2)$ when $n\alpha \ge 1$; integrating over $\alpha$ (the values $\alpha < 1/n$ contributing at most $1/n$) gives $O(1/(n+1))$. (Derived, not stated by Knudsen and Stöckel: the same fourth-moment argument applies to a five-wise independent family with values in $\{0, \dots, q-1\}$ and ties counted toward the event, giving the explicit bound $7/|S|$ for $0 < |S| \le q$ and $x \notin S$.)

## Sources

- M. B. T. Knudsen and M. Stöckel, "Quicksort, Largest Bucket, and Min-Wise Hashing with Limited Independence", European Symposium on Algorithms (ESA 2015), LNCS 9294, 2015; arXiv:1502.05729: Section 1 (definition of $k$-independence), Section 3 (Table 1) and Theorem 2 (the $5$-independent case), with its proof.
