# Kim–Vu concentration of positive polynomials (Main Theorem)

For every $k$ there is a constant $C > 0$ such that the following holds. Let $t_1, \dots, t_n$ be independent $\{0,1\}$ random variables with $\mathbb E t_i = p_i$, and let $Y = \sum_{e \in E} w(e) \prod_{i \in e} t_i$ have positive weights and edges of size at most $k$. With the [maximal average effects](max-average-effect.md) $E_j$, $E = \max_{j \ge 0} E_j$ and $E' = \max_{j \ge 1} E_j$, for every $\lambda > 1$

$$\Pr\Big[\,|Y - \mathbb E Y| > a_k (E E')^{1/2} \lambda^k\Big] \le C\, e^{-\lambda + (k-1)\log n}, \qquad a_k = 8^k (k!)^{1/2}.$$

The paper writes the right side as $O(\exp(-\lambda + (k-1)\log n))$; its proof gives an explicit constant $d_k$. It also allows some $t_i$ to be constants $p_i$; the statement here is the case, singled out there, where every $t_i$ is a $\{0,1\}$ variable.

For the number $Y$ of triangles in $G(n, p)$ with $p = n^{\varepsilon - 1}$, $0 < \varepsilon < 1/3$, the worst-case effect of an edge, $(n-2)(1-p)$, exceeds $\mathbb E Y$, so Azuma's inequality says nothing; but $E_j \le 1$ for $j \ge 1$, and Kim–Vu gives $\Pr[|Y - \mathbb E Y| > a_3 (\mathbb E Y)^{1/2} \lambda^3] = O(e^{-\lambda + 2 \log n})$.

## Background

- [Azuma's inequality](../azuma-inequality.md): the bound in terms of maximal effects that Kim and Vu recall as their Theorem 1.1 and improve upon.
- [McDiarmid's bounded-differences inequality](../mcdiarmid-s-inequality/mcdiarmid-one-sided-finite-iid.md): the worst-case-effect inequality that this theorem replaces by average effects.
- [Law of a random subset with independent elements](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law.md): the product-Bernoulli model of the variables $t_i$.

## Sources

- J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its applications", *Combinatorica* 20 (2000), 417–434, Section 1.2 (Main Theorem) and Section 1.3 (triangle counts); Section 3 (proof, constants $c_k$, $d_k$).
