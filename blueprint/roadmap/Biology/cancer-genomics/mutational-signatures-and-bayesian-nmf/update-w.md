# ARD multiplicative update of W

For a real $\phi$, real matrices $V, H, W$ and relevances $\lambda_k$, the updated matrix $W'$ has entries

$$w'_{fk} = w_{fk}\, \frac{\sum_{n} v_{fn} h_{kn} / (WH)_{fn}}{\sum_n h_{kn} + \phi / \lambda_k},$$

with the convention $x/0 = 0$ (Tan and Févotte, arXiv:1111.6085v3, Algorithm 2).

## Sources

- V. Y. F. Tan and C. Févotte, *Automatic relevance determination in nonnegative matrix factorization with the β-divergence*, IEEE Trans. Pattern Anal. Mach. Intell. 35 (2013), 1592–1605; arXiv:1111.6085v3, Algorithm 2.
