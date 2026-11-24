# Splitting periodic identity-product tuples by smallest period

Let $G$ be a finite
group, $n$ a natural number and $k \ge 1$. Say that $x = (x_0, \dots, x_{n-1}) \in G^n$ has
period $l$ if $x_{i+l} = x_i$ for all $i$, with indices taken mod $n$. Let $A_k$ be the set of
tuples $x$ with $x_0 x_1 \cdots x_{n-1} = 1$ and period $k$, and for $d \ge 1$ let $P_d$ be the
set of tuples $x$ with $x_0 x_1 \cdots x_{n-1} = 1$ that have period $d$ but no period $l$ with
$0 < l < d$. Then $|A_k| = \sum_{d \mid k} |P_d|$.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 14, with `A_k`, `P_k` as in equation (9) of the arXiv text (`jis-2026-26.4.6-lem-14`).
