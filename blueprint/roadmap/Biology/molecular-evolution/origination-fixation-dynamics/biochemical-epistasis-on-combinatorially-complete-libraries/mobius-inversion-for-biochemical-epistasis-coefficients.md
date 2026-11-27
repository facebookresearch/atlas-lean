# Möbius inversion for biochemical epistasis coefficients

Fix $L$ mutations and identify a genotype with the subset $s \subseteq [L] = \{1, \dots, L\}$ of mutations it carries. Let $y(s)$ be a phenotype on all $2^L$ genotypes, for example $y(s) = -\log_{10} K_{D,s}$, which is proportional to a binding free energy so that non-interacting mutations add. The **biochemical (local) epistasis model of order $K$** is

$$y(s) = \beta_\emptyset + \sum_{\substack{c \subseteq s \\ 1 \le |c| \le K}} \beta_c ,$$

i.e. $y(s) = \beta_0 + \sum_{i=1}^K \sum_{c \in C_i} \beta_c x_{c,s}$ with $C_i$ the $i$-subsets of $[L]$ and $x_{c,s} = \mathbf 1[c \subseteq s]$; $\beta_{\{j\}}$ is the effect of mutation $j$ on the ancestral background and $\beta_c$, $|c| \ge 2$, an interaction coefficient.

**Theorem.** For $K = L$ the model fits every function $y$ exactly, with unique coefficients

$$\beta_c = \sum_{b \subseteq c} (-1)^{|c| - |b|}\, y(b), \qquad c \subseteq [L].$$

In particular $\beta_{\{i,j\}} = y(\{i,j\}) - y(\{i\}) - y(\{j\}) + y(\emptyset)$, the usual pairwise epistasis on the ancestral background. A model of order $K < L$ is exact iff $\beta_c = 0$ for all $|c| > K$, with $\beta_c$ given by the same formula.

## Expansion

The map $\beta \mapsto y$, $y(s) = \sum_{c \subseteq s} \beta_c$, is summation over the Boolean lattice of subsets; by Möbius inversion on that lattice, whose Möbius function is $\mu(b, c) = (-1)^{|c| - |b|}$ for $b \subseteq c$, its inverse is the stated alternating sum. Concretely, substituting gives $\sum_{b \subseteq c} (-1)^{|c|-|b|} \sum_{a \subseteq b} \beta_a = \sum_{a \subseteq c} \beta_a \sum_{a \subseteq b \subseteq c} (-1)^{|c| - |b|}$, and the inner sum is $(1 - 1)^{|c \setminus a|}$, which is $1$ if $a = c$ and $0$ otherwise. Both sides have $2^L$ coordinates, so the linear map is a bijection. Moulana et al. measure all $2^{15} = 32768$ intermediates between the Wuhan Hu-1 and Omicron BA.1 receptor-binding domains, choose $K = 5$ by ten-fold cross-validation, and contrast this "biochemical" reference with the "statistical" (ensemble) parametrization, whose baseline is the library mean, and with a logistic global-epistasis transform for diminishing returns.

## Sources

- A. Moulana, T. Dupic, A. M. Phillips et al., "Compensatory epistasis maintains ACE2 affinity in SARS-CoV-2 Omicron BA.1", Nature Communications 13 (2022), Methods "Epistasis analysis", Eqs. (8)–(9), <https://doi.org/10.1038/s41467-022-34506-z>, PMCID PMC9668218.
