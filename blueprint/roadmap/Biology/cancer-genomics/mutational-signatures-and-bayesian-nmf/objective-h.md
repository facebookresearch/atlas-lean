# H-dependent part of the ARD-NMF objective

For a real $\phi$ (the dispersion), real matrices $V, W, H$ and relevances $\lambda_k$ ($k \in K$), put

$$C_H(H) = \frac{D_1(V \mid WH)}{\phi} + \sum_{k \in K} \sum_{n \in N} \frac{h_{kn}}{\lambda_k},$$

where $D_1$ is the [data-fit term](data-fit.md), with the convention $x/0 = 0$ (Tan and Févotte, arXiv:1111.6085v3, Eq. 20 with $\beta = 1$).

## Sources

- V. Y. F. Tan and C. Févotte, *Automatic relevance determination in nonnegative matrix factorization with the β-divergence*, IEEE Trans. Pattern Anal. Mach. Intell. 35 (2013), 1592–1605; arXiv:1111.6085v3, Eq. 20.
