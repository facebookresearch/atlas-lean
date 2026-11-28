# Christiansen's criterion for protection of an allele under migration and selection

**Model.** A diploid population with two alleles $A_1, A_2$ occupies $\Gamma$ demes. In deme $\alpha$ the genotypes $A_1A_1$, $A_1A_2$, $A_2A_2$ have relative viabilities $x_\alpha$, $1$, $y_\alpha$ with $x_\alpha\ge0$ and $y_\alpha>0$. Let $p_\alpha$ be the frequency of $A_1$ in deme $\alpha$ and $M=(m_{\alpha\beta})$ the irreducible stochastic **backward migration matrix** ($m_{\alpha\beta}$ is the probability that an adult in deme $\alpha$ came from deme $\beta$). Selection followed by migration gives

$$p_\alpha^\ast=\frac{p_\alpha(1-p_\alpha+x_\alpha p_\alpha)}{x_\alpha p_\alpha^2+2p_\alpha(1-p_\alpha)+y_\alpha(1-p_\alpha)^2},\qquad p_\alpha'=\sum_\beta m_{\alpha\beta}\,p_\beta^\ast .$$

The allele $A_1$ is **protected** if the monomorphic state $p=0$ is unstable. The linearization at $p=0$ is $p'=Qp$ with

$$Q=MD,\qquad D=\operatorname{diag}(y_1^{-1},\dots,y_\Gamma^{-1}),\qquad q_{\alpha\beta}=\frac{m_{\alpha\beta}}{y_\beta}.$$

$Q$ is non-negative and irreducible, so it has a Perron–Frobenius eigenvalue $\lambda_0>0$, and $A_1$ is protected if $\lambda_0>1$ and not protected if $\lambda_0<1$, with $\min_\alpha\sum_\beta q_{\alpha\beta}\le\lambda_0\le\max_\alpha\sum_\beta q_{\alpha\beta}$.

**Theorem (Christiansen).** Let $I^{(n)}$ be the $n\times n$ identity and $Q^{(n)}$ the leading $n\times n$ submatrix of $Q$. If for some ordering of the demes and some $1\le n\le\Gamma$

$$\det\bigl(I^{(n)}-Q^{(n)}\bigr)<0,$$

then $A_1$ is protected. The criterion is sharp: if the reversed inequality holds for every $n\le\Gamma$, then $A_1$ is not protected.

**Consequences.**

- ($n=1$, Deakin) $A_1$ is protected if some deme satisfies $m_{\alpha\alpha}>y_\alpha$.
- If $y_\alpha\ge1$ in every deme and $y_\beta>1$ in some deme ($A_2A_2$ never less fit than the heterozygote), then $\lambda_0<1$ and $A_1$ is not protected, whatever the $x_\alpha$.
- If $A_2$ is completely dominant ($y_\alpha=1$ for all $\alpha$), then $\lambda_0=1$ and linearization is inconclusive.
- Protection of $A_2$ is decided by the same criterion with $y_\beta$ replaced by $x_\beta$; both alleles protected gives a protected polymorphism.

## Depends on

- [Protected polymorphism in the Levene model](../migration-and-selection/protected-polymorphism-in-the-levene-model.md)

## Expansion

For a non-negative irreducible matrix $Q$, $\lambda_0<1$ if and only if $I-Q$ is a non-singular M-matrix, which for a Z-matrix is equivalent to positivity of all leading principal minors; when $\lambda_0=1$ the proper leading principal minors are still positive and the determinant vanishes. Hence a negative minor $\det(I^{(n)}-Q^{(n)})$ in some ordering forces $\lambda_0>1$, and positivity of all leading minors forces $\lambda_0<1$. The $n=1$ case says that a deme which retains its own residents with probability exceeding the relative fitness of $A_2A_2$ is a refuge for the rare allele. In the Levene model, $m_{\alpha\beta}=c_\beta$, the criterion reduces to $\sum_\beta c_\beta/y_\beta>1$, the harmonic-mean condition.

## Sources

- Reinhard Bürger, "A Survey on Migration-Selection Models in Population Genetics", *Discrete and Continuous Dynamical Systems, Series B* 19 (2014), 883–959, <https://doi.org/10.3934/dcdsb.2014.19.883>; preprint arXiv:1309.2576, <https://doi.org/10.48550/arXiv.1309.2576>. Numbering of the journal version: Section 3.1 (recurrence equations), Section 4.1 (linearization $Q=MD$, Perron–Frobenius criterion, Example 8), Section 4.3 (Theorem 13, after Christiansen 1974, and Deakin's condition).
