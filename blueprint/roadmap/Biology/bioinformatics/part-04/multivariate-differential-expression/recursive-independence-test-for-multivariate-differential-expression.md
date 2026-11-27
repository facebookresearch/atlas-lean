# Recursive independence test for multivariate differential expression

Let $X = (X_1,\dots,X_n)$ be gene expression levels and $Y$ a class label (e.g. disease status). Gene $X_i$ is **univariately differentially expressed** (UDE) if $X_i \not\perp Y$, and **multivariately differentially expressed** (MDE) if

$$\exists\, S \subseteq X \setminus \{X_i\}:\quad X_i \not\perp Y \mid S,$$

i.e. it carries information about $Y$ in some context of other genes. The MDE set $M$ contains every gene relevant to $Y$, including genes that are redundant for prediction, and in general requires an exhaustive subset search.

A distribution is **PCWT** if it is strictly positive and its independence relation satisfies the composition and weak transitivity properties (in addition to the semi-graphoid axioms).

**Theorem 1 (reachability).** For any PCWT distribution, $M$ equals the set of genes $X_k$ for which there is a sequence $Y = Z_1, Z_2, \dots, Z_m = X_k$ of variables with $Z_i \not\perp Z_{i+1}$ (marginal dependence) for $i = 1, \dots, m-1$.

**Theorem 2.** Every strictly positive distribution faithful to a Bayesian network is PCWT.

**Theorem 3.** If $X'$ is PCWT and $S, T$ are disjoint subsets of its components, then with probability $1$ the distribution of $X' \setminus (S \cup T)$ conditional on $T = t$ is PCWT.

**Recursive independence test (RIT).** Test $X_i \perp Y$ for all genes, keep the significant set $S_1$; for each newly added gene $X_i$ test $X_i \perp X_j$ against all genes not yet selected and add the significant ones; recurse until no gene is added. By Theorem 1, RIT is consistent for $M$ whenever the marginal tests are consistent; it performs on the order of $|\hat M|\, n$ tests, and multiplicity is controlled at level $\alpha$ by applying a false-discovery-rate correction within each round.

## Depends on

- [Symmetry of conditional independence](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/cond-indep-symm.md)

## Expansion

Composition lets dependence of $X_k$ on $Y$ given some set be traced to a single variable in that set, and weak transitivity propagates dependence along chains; together they turn conditional dependence on arbitrary contexts into reachability in the graph of pairwise marginal dependencies. Theorems 2–3 justify the PCWT assumption for transcript measurements: a cellular network of transcripts, proteins and metabolites modelled as a faithful Bayesian network is PCWT, and observing only transcripts (marginalizing the rest) or holding some variables fixed preserves the class. Without PCWT, a gene can be MDE yet unreachable, as in XOR-type interactions.

## Sources

- R. Nilsson, J. M. Peña, J. Björkegren and J. Tegnér, "Detecting multivariate differentially expressed genes", BMC Bioinformatics 8 (2007), 150, Eq. (2), the RIT algorithm and Theorems 1–3, <https://doi.org/10.1186/1471-2105-8-150>, PMCID: PMC1885271.
