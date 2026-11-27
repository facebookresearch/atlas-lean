# Dynamic-programming chaining of collinear gene pairs

Let two chromosomes carry genes indexed by their ranks $1, 2, \dots$ along each chromosome, and let $A$ be a finite set of anchors: matched gene pairs $v = (i_v, j_v)$, where $i_v$ is the rank on the first chromosome and $j_v$ the rank on the second (homology from all-against-all protein similarity search, after collapsing tandem arrays to one representative pair). For the same-orientation pass, say that $u$ precedes $v$ if $i_u < i_v$ and $j_u < j_v$, and let the number of gaps between them be

$$\operatorname{gaps}(u, v) = \max\big(i_v - i_u - 1,\; j_v - j_u - 1\big),$$

the larger number of intervening genes. Given a match score $\mathrm{MatchScore}(v) > 0$, a gap penalty $\mathrm{GapPenalty} < 0$ and a maximum gap $g_{\max}$, define the chain score recursively over anchors sorted by $i_v$:

$$\mathrm{Score}(v) = \max\Big(\mathrm{MatchScore}(v),\; \max_{u \text{ precedes } v,\; \operatorname{gaps}(u,v) < g_{\max}} \big[\mathrm{Score}(u) + \mathrm{MatchScore}(v) + \operatorname{gaps}(u, v)\cdot \mathrm{GapPenalty}\big]\Big).$$

Then $\mathrm{Score}(v)$ is the maximum, over all chains $u_1 \prec u_2 \prec \dots \prec u_k = v$ of anchors with consecutive gaps below $g_{\max}$, of $\sum_{l} \mathrm{MatchScore}(u_l) + \mathrm{GapPenalty}\sum_{l<k}\operatorname{gaps}(u_l, u_{l+1})$, and it is computed for all anchors in $O(|A|^2)$ time. Collinear blocks are the highest-scoring non-overlapping chains, extracted greedily, whose score is at least a reporting threshold $\theta$; reversed blocks are found by the same recursion with $j$ replaced by $-j$. In the MCScanX defaults, $\mathrm{MatchScore} = 50$, $\mathrm{GapPenalty} = -1$, $g_{\max} = 25$ and a block needs at least five collinear gene pairs. A chain of five gapless anchors scores exactly $5 \cdot 50 = 250$, so taking $\theta = 250$ with a non-strict comparison admits it; the source's description does not settle this boundary case, and the non-strict comparison is the convention adopted here.

## Expansion

The precedence relation is a strict partial order on anchors, and the score of a chain is additive over its anchors and its consecutive gaps, so the best chain ending at $v$ either consists of $v$ alone or extends the best chain ending at some admissible predecessor $u$; this is the optimal-substructure property that justifies the recursion. Processing anchors in increasing $i$ ensures that every predecessor has already been scored. Storing the maximizing predecessor and backtracking from the best endpoint recovers the chain; removing its anchors and repeating yields non-overlapping blocks. The significance of a block is assessed separately by an expected number of chance occurrences computed from the number of anchors and the spacing of matches in the two regions.

## Sources

- Y. Wang, H. Tang, J. D. DeBarry, X. Tan, J. Li, X. Wang, T.-h. Lee, H. Jin, B. Marler, H. Guo, J. C. Kissinger and A. H. Paterson, MCScanX: a toolkit for detection and evolutionary analysis of gene synteny and collinearity, *Nucleic Acids Res.* 40 (2012), e49, <https://doi.org/10.1093/nar/gkr1293>, PMCID PMC3326336 (Materials and Methods, the MCScanX algorithm).
