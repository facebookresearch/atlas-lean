# Orthogonal rotations of factor loadings leave the covariance unchanged

In the factor model $\Sigma = \Lambda\Lambda^{\mathsf T} + \Psi$ for a $p \times k$ loading matrix $\Lambda$ with uncorrelated standardized factors, every orthogonal $k \times k$ matrix $Q$ gives $(\Lambda Q)(\Lambda Q)^{\mathsf T} = \Lambda\Lambda^{\mathsf T}$, so the loadings $\Lambda$ and $\Lambda Q$ give the same covariance matrix and the orientation of the loadings is not identified from $\Sigma$. For $k = 1$ the orthogonal matrices are $\pm 1$, so the loadings can at best be identified up to a common sign; whether they are identified up to sign needs further assumptions, such as those of the three-indicator model.

## Background

- [Identification of a one-factor model from three indicators](identification-of-the-one-factor-model.md): conditions under which the one-factor loadings are identified up to sign.

## Sources

- J. Brunner, *Confirmatory factor analysis, part 1*, STA 431 lecture slides, University of Toronto, 2023, slides 3–4 and 13, <http://utstat.utoronto.ca/brunner/oldclass/431s23/lectures/431s23CFA1.pdf>
