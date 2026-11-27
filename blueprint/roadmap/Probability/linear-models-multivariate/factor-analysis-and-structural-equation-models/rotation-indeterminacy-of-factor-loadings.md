# Orthogonal rotations of factor loadings leave the covariance unchanged

Let $\Lambda$ be a real loading matrix with rows indexed by the indicators and $k$ columns, one per factor, let $\Theta$ be any real square matrix indexed by the indicators, and let $U$ be a real $k \times k$ matrix with $UU^{\mathsf T} = I$. With identity factor covariance $\Phi = I$, the [covariance implied by the factor model](factor-model-reparametrization-and-group-invarian/factor-model-cov.md), $\Lambda\Phi\Lambda^{\mathsf T} + \Theta$, is the same for the loadings $\Lambda U$ as for $\Lambda$: $(\Lambda U)(\Lambda U)^{\mathsf T} + \Theta = \Lambda\Lambda^{\mathsf T} + \Theta$. So the orientation of the loadings is not identified from the covariance. For $k = 1$ the orthogonal matrices are $\pm 1$, so the loadings can at best be identified up to a common sign; whether they are identified up to sign needs further assumptions, such as those of the three-indicator model.

## Background

- [Identification of a one-factor model from three indicators](identification-of-the-one-factor-model.md): conditions under which the one-factor loadings are identified up to sign.

## Sources

- J. Brunner, *Confirmatory factor analysis, part 1*, STA 431 lecture slides, University of Toronto, 2023, slides 3–4 and 13, <http://utstat.utoronto.ca/brunner/oldclass/431s23/lectures/431s23CFA1.pdf>
