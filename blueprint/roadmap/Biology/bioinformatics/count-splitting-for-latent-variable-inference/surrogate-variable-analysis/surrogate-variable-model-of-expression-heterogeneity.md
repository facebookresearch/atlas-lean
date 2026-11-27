# Surrogate variable model of expression heterogeneity

Let $x_{ij}$ be the expression of gene $i \in \{1,\dots,m\}$ on array $j \in \{1,\dots,n\}$, $n < m$, and $y_j$ the primary variable. Suppose
there are $L$ unmodeled factors whose (arbitrarily nonlinear) effects across arrays are vectors $g_\ell = (g_{\ell 1}, \dots, g_{\ell n})$,
$\ell = 1, \dots, L$, with gene-specific coefficients $\gamma_{\ell i}$ ($\gamma_{\ell i} = 0$ if factor $\ell$ does not affect gene $i$):

$$x_{ij} = \mu_i + f_i(y_j) + \sum_{\ell=1}^L \gamma_{\ell i}\, g_{\ell j} + e^*_{ij},$$

where the $e^*_{ij}$ are gene-specific noise, approximately independent across genes; the sum captures the dependence across genes
(*expression heterogeneity*). Since each gene has $n$ observations, at most $n$ such vectors are linearly independent, so $L \le n$
suffices for any dependence structure.

**Lemma (surrogate variables).** For any vectors $g_1, \dots, g_L \in \mathbb{R}^n$ and coefficients $\gamma_{\ell i}$ there exist
$K \le L$ mutually orthogonal vectors $h_1, \dots, h_K \in \mathbb{R}^n$ and coefficients $\lambda_{k i}$ with

$$\sum_{\ell=1}^L \gamma_{\ell i}\, g_{\ell j} = \sum_{k=1}^K \lambda_{k i}\, h_{k j} \quad \text{for all } i, j;$$

one choice is the right singular vectors with nonzero singular values (from a [singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)) of the $m \times n$ matrix with entries
$\sum_\ell \gamma_{\ell i} g_{\ell j}$. The $h_k$ are called **surrogate variables**; only their span, not the individual factors $g_\ell$,
needs to be estimated.

## Expansion

The matrix $\Gamma G$ with $\Gamma = (\gamma_{\ell i})^\top \in \mathbb{R}^{m \times L}$ and $G = (g_{\ell j}) \in \mathbb{R}^{L \times n}$ has rank
$K \le L$. Its thin singular value decomposition $\Gamma G = U D V^\top$ gives $\Gamma G = (U D) V^\top$ with $V \in \mathbb{R}^{n \times K}$
orthonormal; take $h_k$ the $k$-th column of $V$ and $\lambda_{ki} = (UD)_{ik}$. Fitting $x_{ij} = \mu_i + f_i(y_j) + \sum_k \lambda_{ki} h_{kj}$
with these **true** $h_k$ (or any vectors whose span contains the row span of $\Gamma G$) therefore removes the gene-gene dependence induced by
the unmodeled factors from the error term exactly. Surrogate variables estimated from data need not span this row space: a factor missed by the
estimate remains in the residual, so adjustment by estimated surrogate variables removes this dependence only to the extent that their span
captures the row span of $\Gamma G$. (Leek and Storey 2007, Materials and Methods, model and surrogate-variable reparametrization.)

## Depends on

- [Real singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)

## Sources

- J. T. Leek and J. D. Storey, "Capturing Heterogeneity in Gene Expression Studies by Surrogate Variable Analysis", PLoS Genetics (2007), <https://doi.org/10.1371/journal.pgen.0030161> (PMC1994707).
