# Hu's independent-set formula for the coprimality density

Let $k$ be a natural number, let
$E$ be a set of pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$
with edge set $E$, and let $A_G$ be its coprimality density. For $0 \le m \le k$, let $i_m(G)$ be
the number of independent sets of $G$ of size $m$, that is, of sets $S \subseteq \{1, \dots, k\}$
with $|S| = m$ such that no edge of $E$ has both endpoints in $S$. Then

$$A_G = \prod_p \sum_{m=0}^{k} \frac{i_m(G)}{p^m} \left(1 - \frac{1}{p}\right)^{k-m},$$

the product running over all primes $p$.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`).
