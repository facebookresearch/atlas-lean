# Joint limit law of cherries and pitchforks under the YHK and PDA models

Let $A_n$ and $B_n$ be the numbers of pitchforks and cherries in a random rooted binary phylogenetic tree with $n$ leaves. Under the Yule–Harding–Kingman (YHK) model the tree grows by attaching a new leaf to a uniformly chosen pendant edge; under the proportional-to-distinguishable-arrangements (PDA) model, to a uniformly chosen edge of any kind.

**Theorem.** For any initial tree $T_m$ ($m \ge 2$) from which the process is run:
1. (YHK) $\frac1n(A_n,B_n) \to \big(\tfrac16,\tfrac13\big)$ almost surely, and

$$\frac{(A_n,B_n) - n(1/6, 1/3)}{\sqrt n} \xrightarrow{d} N\!\left(0,\ \frac{1}{1260}\begin{pmatrix}69 & -28\\ -28 & 56\end{pmatrix}\right).$$

2. (PDA) $\frac1n(A_n,B_n) \to \big(\tfrac18,\tfrac14\big)$ almost surely, and

$$\frac{(A_n,B_n) - n(1/8, 1/4)}{\sqrt n} \xrightarrow{d} N\!\left(0,\ \frac{1}{64}\begin{pmatrix}3 & 0\\ 0 & 4\end{pmatrix}\right),$$

so under PDA the two counts are asymptotically independent.
3. The same limits hold for unrooted trees grown from any initial unrooted tree with $m \ge 6$ leaves.

In particular the limits do not depend on the initial tree. They are consistent with the exact YHK moments for $n \ge 7$: $E A_n = n/6$, $E B_n = n/3$, $\operatorname{Var}A_n = 23n/420$, $\operatorname{Var}B_n = 2n/45$, $\operatorname{Cov}(A_n,B_n) = -n/45$.

## Proof depends on

- [Limit theorems for strictly balanced small urn models](limit-theorems-for-strictly-balanced-small-urns.md)

## Expansion

Under YHK, classify pendant edges into four types: in a cherry that lies in a pitchfork (type 1), in a cherry not in a pitchfork (type 2), in a pitchfork but not a cherry (type 3), and in neither (type 4). Attaching a leaf to a pendant edge changes the type counts by a fixed vector depending only on the chosen edge's type, so the type vector $\alpha(T_n)$ is a four-color urn with a replacement matrix of eigenvalues $1, 0, -2, -3$ and principal left eigenvector $v_1 = (\tfrac13,\tfrac13,\tfrac16,\tfrac16)$; it satisfies (A1)–(A4), so the urn limit theorems give the strong law and a CLT for $\alpha(T_n)$ with an explicit $4\times4$ covariance. Pitchforks and independent cherries are half the type 1 and type 2 counts, and cherries are half the type 1 plus type 2 counts, which yields the stated limits by a linear map. Under PDA all edges can receive the new leaf, so a six-type edge partition is needed; its replacement matrix has eigenvalues $2, 0, 0, 0, -2, -4$ and principal left eigenvector $\tfrac1{16}(2,2,1,3,1,7)$. The unrooted case reduces to the rooted one by conditioning on the two possible six-leaf shapes.

## Sources

- K. P. Choi, G. Kaur, T. Wu, "On asymptotic joint distributions of cherries and pitchforks for random phylogenetic trees", Journal of Mathematical Biology (2021), Theorems 3–6, Corollaries 1–2, Eqs. (8)–(27), <https://doi.org/10.1007/s00285-021-01667-2>, PMCID PMC8460594.
