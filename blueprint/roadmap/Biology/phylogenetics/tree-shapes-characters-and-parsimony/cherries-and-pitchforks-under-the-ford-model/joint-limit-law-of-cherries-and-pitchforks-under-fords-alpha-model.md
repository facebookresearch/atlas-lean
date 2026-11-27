# Joint limit law of cherries and pitchforks under Ford's alpha model

**Model.** Fix $\alpha \in [0,1]$. Ford's alpha model grows a rooted binary phylogenetic tree one leaf at a time from a two-leaf tree $T_2$: given $T_m$, choose an edge with weight $1-\alpha$ for each pendant edge and $\alpha$ for each other edge (including the root edge), i.e. a pendant edge with probability $(1-\alpha)/(m-\alpha)$ and an internal edge with probability $\alpha/(m-\alpha)$, and attach the new leaf at its midpoint. The cases $\alpha = 0$, $\alpha = 1/2$ and $\alpha = 1$ are the Yule, uniform (PDA) and comb models. A *cherry* is a fringe subtree with exactly two leaves and a *pitchfork* a fringe subtree with exactly three leaves; let $C_n$ and $A_n$ be their numbers in $T_n$.

**Theorem.** For every $\alpha \in [0,1]$,

$$\frac{1}{n}(A_n, C_n) \xrightarrow{\text{a.s.}} (\nu,\mu) = \frac{1-\alpha}{2(3-2\alpha)}\,(1, 2),$$

and

$$\frac{(A_n, C_n) - n(\nu,\mu)}{\sqrt n} \xrightarrow{d} \mathcal{N}\big((0,0), S\big), \qquad S = \frac{1-\alpha}{(3-2\alpha)^2(5-4\alpha)}\begin{pmatrix} \dfrac{-24\alpha^3 + 96\alpha^2 - 135\alpha + 69}{4(7-4\alpha)} & -\dfrac{(2-\alpha)(1-2\alpha)}{2} \\[1ex] -\dfrac{(2-\alpha)(1-2\alpha)}{2} & 2-\alpha \end{pmatrix}.$$

**Corollary.**

1. For $0 \le \alpha < 1$, $A_n / C_n \to 1/2$ almost surely.
2. $A_n/n \to (1-\alpha)/(2(3-2\alpha))$, which decreases strictly from $1/6$ (Yule) to $0$ (comb) as $\alpha$ goes from $0$ to $1$.
3. The limiting variance $\tau^2$ of $A_n/\sqrt n$ decreases strictly from $23/420$ to $0$ on $[0,1]$.
4. The limiting covariance of $(A_n,C_n)/\sqrt n$ is negative for $\alpha < 1/2$, zero at $\alpha = 1/2$ (asymptotic independence under the uniform model), positive for $1/2 < \alpha < 1$, and zero at $\alpha = 1$, where $S = 0$.

## Expansion

Color each edge of the growing tree by its role (pendant edge in a cherry, in a pitchfork, elsewhere, internal edges above cherries and pitchforks, other internal edges); attaching a leaf to an edge of a given color changes the color counts by a fixed vector, so the color counts form a six-color generalized Pólya urn whose replacement matrix has some negative entries. For $\alpha \in (0,1)$ the drawing probabilities are non-uniform ($1-\alpha$ versus $\alpha$), which is handled by an equivalent uniform urn with replacement matrix $R P_\alpha$ (a reweighting $P_\alpha$ of the colors). The strong law and CLT for such urns (principal eigenvalue $1$ and spectral gap) give the almost-sure limit from the left principal eigenvector and the covariance from the remaining eigenstructure; the pitchfork and cherry counts are linear functions of the color counts.

## Sources

- Gursharn Kaur, Kwok Pui Choi and Taoyang Wu, "Distributions of cherries and pitchforks for the Ford model", Theoretical Population Biology 149 (2023), 27–38, <https://doi.org/10.1016/j.tpb.2022.12.002>; numbering as in arXiv:2110.02850: Theorems 3.1, 3.2, 3.4 and Corollary 3.3 (Section 3), Corollary 4.7.
