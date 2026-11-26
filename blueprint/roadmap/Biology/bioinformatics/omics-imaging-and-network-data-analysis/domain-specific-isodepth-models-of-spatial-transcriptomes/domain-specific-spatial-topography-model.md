# Domain-specific spatial topography model

Let a tissue slice $T \subseteq \mathbb{R}^2$ be partitioned into $P$ spatial domains $R_1, \dots, R_P$ with indicator (assignment) functions $w_p : \mathbb{R}^2 \to \{0, 1\}$, $\sum_p w_p = 1$ on $T$. Model each gene's expression $f_g$ as piecewise continuously differentiable with the same pieces for every gene, $f_g = \sum_p f_{p,g}\, w_p$. Assume that within each domain all genes share one conservative gradient field: $\nabla f_{p,g} = \beta_{p,g} \nabla d_p$ for a continuously differentiable **domain-$p$ isodepth** $d_p$ and constants $\beta_{p,g}$. Integrating gives

$$f_g(x, y) = \sum_{p=1}^{P} \big(\beta_{p,g}\, d_p(x, y) + \alpha_{p,g}\big)\, w_p(x, y),$$

so each domain-wise expression function is a linear function $h_{p,g}(z) = \beta_{p,g} z + \alpha_{p,g}$ of its own isodepth, while no relation is imposed between the domains' shapes and the isodepths, and the tissue-wide gradient field may be discontinuous across domain boundaries.

**Domain-specific spatial topography problem.** Given counts $a_{i,g}$ at spot locations $(x_i, y_i)$, $i = 1, \dots, N$, and a number $P$ of domains, find assignment functions $w_p$, isodepths $d_p \in C^1(\mathbb{R}^2, \mathbb{R})$ and linear $h_{p,g}$ maximizing

$$\sum_{g=1}^{G} \sum_{i=1}^{N} \log \mathbb{P}\Big(a_{i,g} \ \Big|\ \sum_{p=1}^{P} h_{p,g}\big(d_p(x_i, y_i)\big)\, w_p(x_i, y_i)\Big).$$

## Expansion

The model strictly generalizes the global isodepth model, which is the special case where all $d_p$ coincide with one field $d$ and each domain is a union of level sets of $d$; in particular it can represent perpendicular gradients in adjacent domains, which a global isodepth cannot ([nonexistence of a global isodepth](nonexistence-of-a-global-isodepth-for-domain-wise-expression.md)). The problem mixes optimization over binary assignment functions and continuous functions, generalizing mixed-integer programming, so it is solved approximately. A spatial mixture-of-experts parametrization fits it: a gating network on $(x, y)$ gives soft domain weights with top-1 hard assignment, and expert $p$ is a neural field $E_p(x, y) = (h_{p,g}(d_p(x, y)))_{g}$ whose last hidden layer has a single unit (the isodepth $d_p$) followed by a linear layer. The learned $d_p$ gives within-domain coordinates along which expression gradients (for example hypoxia or signaling programs in tumor regions) are measured.

## Sources

- U. Chitra, S. Dan, F. Krienen, B. J. Raphael, "GASTON-Mix: a unified model of spatial gradients and domains using spatial mixture-of-experts", Bioinformatics (2025), Section 2.1 (Eqs. 1-2), Section 2.2 (Eq. 3, Theorem 1), Section 2.3 (Eqs. 4-8, domain-specific spatial topography problem), Section 2.4 (spatial mixture-of-experts, Eq. 9). <https://doi.org/10.1093/bioinformatics/btaf254> (PMC12261403)
