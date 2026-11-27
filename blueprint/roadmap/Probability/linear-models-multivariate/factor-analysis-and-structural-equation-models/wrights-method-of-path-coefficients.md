# Wright's path-coefficient rules

Consider a recursive (acyclic) linear structural model of standardized variables, $X_j = \sum_{i \in \mathrm{pa}(j)} p_{ji} X_i + e_j$, with residuals uncorrelated with each other and with the parents of $X_j$, and with correlations between exogenous variables drawn as bidirectional arrows. Wright (1921, 1934) proposed path-tracing rules: the correlation between two variables is the sum, over all path chains connecting them, of a product along the chain: the product of the standardized path coefficients $p_{ji}$ of the directed arrows of the chain, multiplied once by the correlation $\mathrm{Corr}(X_u, X_v)$ if the chain crosses a bidirectional arrow $u \leftrightarrow v$ (for a chain consisting of a lone bidirectional arrow the directed product is $1$). A correlation is not a path coefficient; Wright (1934, p. 163) distinguishes it from the directed coefficients in this product, and Wright (1921, pp. 567–568) makes the same substitution for correlated causes. A chain may trace backward up an arrow and then forward, or forward only, but never forward and then back (it never passes from one arrowhead into another), passes through each variable at most once, and contains at most one bidirectional arrow; the rules assume a model without feedback loops. The rules are a combinatorial reading of the covariance of the model: writing $P$ for the matrix of path coefficients and $\Sigma_e$ for the covariance of the exogenous terms, acyclicity makes $I - P$ invertible with $(I - P)^{-1} = \sum_{m \ge 0} P^m$, and the covariance matrix is $(I - P)^{-1}\Sigma_e (I - P)^{-\top}$. When the exogenous terms are uncorrelated (no bidirectional arrows), expanding this product entrywise writes each covariance as a sum over treks (pairs of directed paths with a common top), and Wright's rules are the equivalent simple-trek rule, in which the chains meet only at the top and each top contributes its variance, here $1$ (Sullivant, Talaska and Draisma 2010, Proposition 2.1 and Eqs. (1)–(2)). [Wright's path formula for the inbreeding coefficient](../../../Biology/quantitative-genetics/pedigree-kinship-and-inbreeding/inbreeding-eq-sum-paths.md), which sums $(\frac12)^{|p| + |p'| - 1}(1 + F_A)$ over pairs of ancestral paths meeting only at a common ancestor $A$, applies the same tracing idea to pedigrees.

## Depends on

- [Solution of the structural equations](../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/solve.md)
- [Covariance matrix](../../high-dimensional-probability/isotropic-constant-of-log-concave-laws/covariance-matrix.md): the covariance matrix of the vector of variables

## Proof depends on

- [Reduced form and covariance of a linear structural equation model](reduced-form-covariance-of-a-linear-sem.md): with $B = P$, no external input and $\Psi = \Sigma_e$, the covariance identity whose product is expanded entrywise

## Expansion

1. The model: a recursive linear structural equation model, standardization, and the path diagram.
2. The covariance matrix $(I - P)^{-1} \Sigma_e (I - P)^{-\top}$ and its expansion as a sum over chains.
3. The tracing rules as a combinatorial description of that expansion, and the variance decomposition of each endogenous variable.
4. The additional rule for unstandardized models.
5. Identification of the path coefficients from the correlations in a recursive model, as a separate statement.

## Sources

- Original result: S. Wright, Correlation and causation, J. Agric. Res. 20 (1921), 557–585.
- Original result: S. Wright, The method of path coefficients, Ann. Math. Statist. 5 (1934), 161–215. <https://doi.org/10.1214/aoms/1177732676>
- S. Sullivant, K. Talaska and J. Draisma, Trek separation for Gaussian graphical models, Ann. Statist. 38 (2010), 1665–1685, Section 2, Proposition 2.1 and Eqs. (1)–(2). <https://doi.org/10.1214/09-AOS760>
