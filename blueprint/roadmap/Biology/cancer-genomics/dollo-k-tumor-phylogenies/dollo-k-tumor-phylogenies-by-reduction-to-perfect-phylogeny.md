# Dollo(k) tumor phylogenies by reduction to perfect phylogeny on an extended matrix

**Dollo(k) model.** Cells are rows and mutations are columns of a binary matrix $M$, possibly with
missing entries. A Dollo(k) phylogeny is a rooted tree in which every mutation $m$ is acquired exactly
once (a node labeled $m^{+}$) and lost at most $k$ times (nodes labeled $m^{-}_{1}, \dots, m^{-}_{k}$); the
state of a leaf is the set of mutations acquired on its root path and not subsequently lost. Dollo(0)
is the perfect phylogeny (infinite sites) model and Dollo(1) the persistent phylogeny model.

**Extended matrix.** Replace each column $j$ by $k + 1$ columns $j^{+}, j^{-}_{1}, \dots, j^{-}_{k}$: where
$M[i, j] = 1$ set $M_e[i, j^{+}] = 1$ and $M_e[i, j^{-}_{l}] = 0$ for all $l$; where $M[i, j]$ is $0$ or missing,
leave all $k + 1$ extended entries missing.

**Proposition.** $M$ has a completion with a Dollo(k) phylogeny if and only if $M_e$ has a completion
$M_e^{*}$ with a perfect phylogeny such that

$$M_e^{*}[i, j^{+}] - \sum_{l \le k} M_e^{*}[i, j^{-}_{l}] = M[i, j] \ \text{ if } M[i, j] \in \{0, 1\}, \qquad
M_e^{*}[i, j^{+}] \ge \sum_{l \le k} M_e^{*}[i, j^{-}_{l}] \ \text{ if } M[i, j] \text{ is missing}.$$

**Maximum likelihood ILP with sequencing noise.** For single-cell data with false-negative rate
$\alpha$ and false-positive rate $\beta$, let binary variables $E(c, m^{\pm})$ encode the completed extended
matrix and $F(c, m) = E(c, m^{+}) - \sum_{i \le k} E(c, m^{-}_{i})$ the inferred genotype. Maximize

$$\sum_{c} \sum_{m} \log w(c, m), \qquad w(c, m) = \begin{cases} (1 - \alpha) F(c, m) + \beta\,(1 - F(c, m)) & I(c, m) = 1, \\ \alpha F(c, m) + (1 - \beta)(1 - F(c, m)) & I(c, m) = 0, \end{cases}$$

subject to no pair of extended columns being in conflict (showing all of $(0,1)$, $(1,0)$, $(1,1)$),
encoded by binary indicators $B(p, q, a, b)$ with $B(p, q, 0, 1) + B(p, q, 1, 0) + B(p, q, 1, 1) \le 2$.
Since $F(c, m)$ is binary, each $\log w(c, m)$ is a linear function of $F(c, m)$.

## Depends on

- [Perfect phylogeny and the four-gamete condition](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md)

## Expansion

Treating each gain and each potential loss of a mutation as its own character turns a tree with losses
into a tree in which every character changes once, from 0 to 1. A leaf carries $m$ exactly when it
lies below the gain and below none of the losses, which is the difference constraint; a loss column
can be 1 only inside the clade of the gain column, which is the inequality for missing entries. The
directed perfect phylogeny condition for complete binary matrices (no conflicting column pair) then
supplies linear constraints. Reconstruction under Dollo is NP-complete in general, so bounding $k$
(with $k = 1$ already capturing the observed rare losses) keeps the ILP size at $(k + 1)$ times the
number of mutations; a hill-climbing step on the ILP solution then improves the likelihood.

## Sources

- S. Ciccolella, M. Soto Gomez, M. D. Patterson, G. Della Vedova, I. Hajirasouliha, P. Bonizzoni,
  "gpps: an ILP-based approach for inferring cancer progression with mutation losses from single cell
  data", BMC Bioinformatics 21(Suppl 1) (2020) 413, Methods, Proposition 1 and Eqs. 3-10,
  <https://doi.org/10.1186/s12859-020-03736-7> (PMC7725124).
