# Wright's path-coefficient rules

Consider a recursive (acyclic) linear structural model of standardized variables, $X_j = \sum_{i \in \mathrm{pa}(j)} p_{ji} X_i + e_j$, with residuals uncorrelated with each other and with the parents of $X_j$, and with correlations between exogenous variables drawn as bidirectional arrows. Wright (1934) proposed path-tracing rules: the correlation between two variables is the sum, over all path chains connecting them, of the products of the standardized path coefficients along the chain, where a chain may trace backward up an arrow and then forward, or forward only, but never forward and then back (it never passes from one arrowhead into another), passes through each variable at most once, and contains at most one bidirectional arrow; the rules assume a model without feedback loops (Path analysis (statistics), Wikipedia, section on path-tracing rules). The rules are a combinatorial reading of the covariance of the model: writing $P$ for the matrix of path coefficients and $\Sigma_e$ for the covariance of the exogenous terms, acyclicity makes $I - P$ invertible with $(I - P)^{-1} = \sum_{m \ge 0} P^m$, and expanding $(I - P)^{-1}\Sigma_e (I - P)^{-\top}$ entrywise lists exactly the admissible chains. [Wright's path formula for the inbreeding coefficient](../../Biology/quantitative-genetics/pedigree-kinship-and-inbreeding/inbreeding-eq-sum-paths.md), which sums $(\frac12)^{|p| + |p'| - 1}(1 + F_A)$ over pairs of ancestral paths meeting only at a common ancestor $A$, applies the same tracing idea to pedigrees.

## Depends on

- [Solution of the structural equations](../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/solve.md)

## Expansion

1. The model: a recursive linear structural equation model, standardization, and the path diagram.
2. The covariance matrix $(I - P)^{-1} \Sigma_e (I - P)^{-\top}$ and its expansion as a sum over chains.
3. The tracing rules as a combinatorial description of that expansion, and the variance decomposition of each endogenous variable.
4. The additional rule for unstandardized models.
5. Identification of the path coefficients from the correlations in a recursive model, as a separate statement.

## Sources

- Path analysis (statistics), Wikipedia, sections on history and on path-tracing rules. <https://en.wikipedia.org/wiki/Path_analysis_(statistics)>
- C. R. Shalizi, Causal modeling, especially graphical causal models, lecture notes, 36-402 Advanced Data Analysis, Carnegie Mellon University.
- Original result: S. Wright, The method of path coefficients, Ann. Math. Statist. 5 (1934), 161–215. <https://doi.org/10.1214/aoms/1177732676> The tracing rules follow Path analysis (statistics), Wikipedia.
