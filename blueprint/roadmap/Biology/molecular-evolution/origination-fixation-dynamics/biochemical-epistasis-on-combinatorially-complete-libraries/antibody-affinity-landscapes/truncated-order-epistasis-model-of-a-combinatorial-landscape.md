# Truncated-order epistasis model of a combinatorial landscape

Let $L$ mutations separate a germline sequence from a somatic sequence, and identify each of the $2^L$ intermediate variants $s$ with its indicator vector $x_s \in \{0,1\}^L$ ($x_{i,s} = 1$ if variant $s$ carries mutation $i$). Let $y_s = -\log_{10} K_{D,s}$ be its log binding affinity, which is proportional to a binding free energy. The interaction model of maximal order $n \le L$ is

$$y_s = \beta_0 + \sum_{i} \beta_i x_{i,s} + \sum_{i<j} \beta_{ij} x_{i,s} x_{j,s} + \dots + \sum_{i_1 < \dots < i_n} \beta_{i_1 \cdots i_n} x_{i_1,s} \cdots x_{i_n,s} + \varepsilon_s,$$

with independent identically distributed errors $\varepsilon_s$. For $n = 1$ this is the additive model. For $n = L$ there are exactly $2^L$ coefficients, one per subset $S$ of mutations, and, without noise, they are determined by the phenotypes through the invertible linear map

$$\beta_S = \sum_{T \subseteq S} (-1)^{|S| - |T|}\, y_T,$$

where $y_T$ is the phenotype of the variant carrying exactly the mutations in $T$. In practice the model is fitted by ordinary least squares at each order $n = 1, 2, \dots$, and the order maximizing cross-validated out-of-sample $R^2$ is selected.

## Expansion

The full model writes $y_T = \sum_{S \subseteq T} \beta_S$, a sum over the subsets of mutations present; Möbius inversion on the Boolean lattice gives the displayed formula, so each $\beta_S$ is the epistatic effect of the set $S$ measured relative to the germline background. Truncating at order $n$ tests whether the landscape is explained by far fewer than $2^L$ parameters, a conservative way to detect higher-order epistasis. Significance of individual coefficients uses a Bonferroni correction over all parameters. For the broadly neutralizing antibody CR9114 (16 mutations, $2^{16} = 65{,}536$ variants), the selected model for binding to H1 hemagglutinin contains strong interactions up to fifth order.

## Sources

- A. M. Phillips, K. R. Lawrence, A. Moulana, T. Dupic, J. Chang, M. S. Johnson, I. Cvijovic, T. Mora, A. M. Walczak and M. M. Desai, "Binding affinity landscapes constrain the evolution of broadly neutralizing anti-influenza antibodies", *eLife* 10 (2021), e71393, Materials and methods section "Linear interaction models", <https://doi.org/10.7554/eLife.71393> (PMC8476123).
