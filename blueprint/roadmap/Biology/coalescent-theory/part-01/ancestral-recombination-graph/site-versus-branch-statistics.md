# Duality between site and branch statistics

Let a tree sequence have marginal trees $T_k$, sample weights $w$ with total $w_{\mathrm{total}}$, and for a node $u$ let $x_k(u)$ be the total weight of the samples below $u$ in $T_k$ and $\beta_k(u)$ the length of the branch above $u$. For a summary function $f$ that is strict, $f(0) = f(w_{\mathrm{total}}) = 0$, Ralph, Thornton and Kelleher (2020) define the site statistic of a site $j$ as $\mathrm{Site}(f, w)_j = \sum_a f(\bar x_j(a))$, the sum over the alleles $a$ at the site of $f$ of the weight carrying $a$ (equation (3)), and the branch statistic of the tree $T_k$ as

$$\mathrm{Branch}(f, w)_k = \sum_{u \in T_k} \beta_k(u)\bigl(f(x_k(u)) + f(w_{\mathrm{total}} - x_k(u))\bigr)$$

(equation (6)), both averaged over a genomic window, the branch statistic with weights proportional to the spans of the trees (equations (4) and (7)). Under the infinite-sites model with mutations at a constant rate $\mu$ in time and along the genome, the expected number of mutations on a branch over a segment is $\mu$ times the segment length times the branch length, and each mutation above $u$ contributes $f(x_k(u)) + f(w_{\mathrm{total}} - x_k(u))$ to the site statistic. Hence, conditionally on the genealogies, the expected site statistic of a window equals $\mu$ times its branch statistic; strictness makes branches ancestral to no sample or to every sample contribute nothing.

## Expansion

1. Sample weights, subtree weights, strict summary functions, and the site and branch statistics of equations (3), (4), (6) and (7).
2. The conditional Poisson mutation model on the branches of each marginal tree, with rate $\mu$ per unit of branch length and of sequence length.
3. The identity of the conditional expectation of the windowed site statistic with $\mu$ times the windowed branch statistic, by linearity over branches.
4. Instances: nucleotide diversity, divergence, the site-frequency spectrum and Patterson's $f_4$ (Fig. 4 of the source).
5. Failure of the identity when two mutations can hit one site, so that the infinite-sites assumption fails.

## Sources

- P. L. Ralph, K. Thornton and J. Kelleher, Efficiently summarizing relationships in large samples: a general duality between statistics of genealogies and genomes, Genetics 215 (2020), 779–797, equations (3), (4), (6), (7), Fig. 4 and the section on branch statistics. <https://doi.org/10.1534/genetics.120.303253>
