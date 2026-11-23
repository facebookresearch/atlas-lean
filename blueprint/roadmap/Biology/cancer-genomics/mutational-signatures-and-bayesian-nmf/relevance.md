# Relevance update in ARD-NMF

For real matrices $W$ ($F \times K$) and $H$ ($K \times N$), reals $b, c$ and a component $k$, the relevance update is

$$\lambda_k = \frac{\sum_f w_{fk} + \sum_n h_{kn} + b}{c},$$

with the convention $x/0 = 0$ (Tan and Févotte, arXiv:1111.6085v3, Eq. 33, where $c = |F| + |N| + a + 1$).

## Sources

- V. Y. F. Tan and C. Févotte, *Automatic relevance determination in nonnegative matrix factorization with the β-divergence*, IEEE Trans. Pattern Anal. Mach. Intell. 35 (2013), 1592–1605; arXiv:1111.6085v3, Eq. 33.
