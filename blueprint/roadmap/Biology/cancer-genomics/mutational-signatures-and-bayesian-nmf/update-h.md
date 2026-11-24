# ARD multiplicative update of H

For a real $\phi$, real matrices $V, W, H$ and relevances $\lambda_k$, the updated matrix $H'$ has entries

$$h'_{kn} = h_{kn}\, \frac{\sum_{f} w_{fk} v_{fn} / (WH)_{fn}}{\sum_f w_{fk} + \phi / \lambda_k},$$

with the convention $x/0 = 0$ (Tan and Févotte, arXiv:1111.6085v3, Eq. 32 and Algorithm 2).

## Sources

- V. Y. F. Tan and C. Févotte, *Automatic relevance determination in nonnegative matrix factorization with the β-divergence*, IEEE Trans. Pattern Anal. Mach. Intell. 35 (2013), 1592–1605; arXiv:1111.6085v3, Eq. 32 and Algorithm 2.
