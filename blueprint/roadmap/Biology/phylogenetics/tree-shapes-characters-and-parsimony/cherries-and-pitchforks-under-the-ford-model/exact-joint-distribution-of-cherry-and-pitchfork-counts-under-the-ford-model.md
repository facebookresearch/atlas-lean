# Exact joint distribution and moments of cherry and pitchfork counts under the Ford model

**Setting.** Under Ford's alpha model with parameter $\alpha \in [0,1]$ (each new leaf attaches to a pendant edge with weight $1-\alpha$ and to any other edge with weight $\alpha$, total weight $n-\alpha$ for a tree with $n$ leaves), let $C_n$ and $A_n$ be the numbers of cherries (two-leaf fringe subtrees) and pitchforks (three-leaf fringe subtrees) of the tree $T_n$ with $n$ leaves.

**Theorem (joint recursion).** For $n \ge 3$, $0 \le a \le n/3$ and $1 \le b \le n/2$,

$$\begin{aligned} \mathbb{P}(A_{n+1}=a, C_{n+1}=b) ={}& \frac{2a + \alpha(n-a-b-1)}{n-\alpha}\,\mathbb{P}(A_n=a, C_n=b) + \frac{(1-\alpha)(a+1)}{n-\alpha}\,\mathbb{P}(A_n=a+1, C_n=b-1) \\ &+ \frac{(2-\alpha)(b-a+1)}{n-\alpha}\,\mathbb{P}(A_n=a-1, C_n=b) + \frac{(1-\alpha)(n-a-2b+2)}{n-\alpha}\,\mathbb{P}(A_n=a, C_n=b-1). \end{aligned}$$

**Theorem (moments).** For $\alpha \in [0,1]$,

$$\mathbb{E}[C_n] = \frac{1-\alpha}{3-2\alpha}\,n + \frac{\alpha}{2(3-2\alpha)} + x_n, \qquad x_n = \frac{\alpha}{2(3-2\alpha)}\prod_{i=3}^{n-1}\frac{i-2+\alpha}{i-\alpha} = O\big(n^{-2(1-\alpha)}\big),$$

$$\mathbb{E}[A_n] = \frac{1-\alpha}{2(3-2\alpha)}\,n + \frac{\alpha}{2(3-2\alpha)} + y_n, \qquad y_n = O\big(n^{-2(1-\alpha)}\big)\ (\alpha<1),$$

and, up to $O(n^{-2(1-\alpha)})$,

$$\operatorname{Var}(C_n) = \frac{(1-\alpha)(2-\alpha)}{(3-2\alpha)^2(5-4\alpha)}\,(n - \alpha),\qquad \operatorname{Cov}(A_n,C_n) = -\frac{(1-\alpha)(2-\alpha)(1-2\alpha)}{2(3-2\alpha)^2(5-4\alpha)}\,n - \frac{\alpha(1-\alpha)(2-\alpha)}{(3-2\alpha)^2(5-4\alpha)},$$

$$\operatorname{Var}(A_n) = \frac{(1-\alpha)(69 - 135\alpha + 96\alpha^2 - 24\alpha^3)}{4(3-2\alpha)^2(5-4\alpha)(7-4\alpha)}\,n + \frac{3\alpha(1-\alpha)(1-2\alpha)(5-3\alpha)}{4(3-2\alpha)^2(5-4\alpha)(7-4\alpha)}.$$

**Corollary (correlation sign).** For each $\alpha \in [0,1/2]$ there is $n_0(\alpha)$ with $\operatorname{corr}(A_n,C_n) < 0$ for all $n > n_0(\alpha)$, and for each $\alpha \in (1/2,1)$ there is $n_0(\alpha)$ with $\operatorname{corr}(A_n,C_n) > 0$ for all $n > n_0(\alpha)$.

## Expansion

Condition on $(A_n,C_n) = (a,b)$ and classify the $n$ leaves' pendant edges and the $n-1$ internal edges by how an insertion there changes the counts: inserting into a pendant edge of a pitchfork's cherry or the pitchfork's single leaf destroys or keeps structures in fixed ways, inserting into a pendant edge of a lone leaf creates a cherry, and so on. Summing the weights $1-\alpha$ or $\alpha$ of the edges of each class, divided by $n-\alpha$, gives the four transition probabilities. Applying the same one-step identity to test functions $\varphi(a,b) \in \{b, a, b^2, ab, a^2\}$ yields linear first-order recurrences for the means and second moments, solved by products of the form $\prod (i-k+\alpha)/(i-\alpha)$, whose $n^{-2(1-\alpha)}$ decay supplies the error terms. The covariance leading coefficient changes sign at $\alpha = 1/2$.

## Sources

- Gursharn Kaur, Kwok Pui Choi and Taoyang Wu, "Distributions of cherries and pitchforks for the Ford model", Theoretical Population Biology 149 (2023), 27–38, <https://doi.org/10.1016/j.tpb.2022.12.002>; numbering as in arXiv:2110.02850: Theorem 4.1, Proposition 4.2, Corollary 4.4, Theorems 4.5–4.6 and Corollary 4.7 (Section 4).
