# The joint law of a pCN step is symmetric

Let $\mu_0$ be a centred Gaussian measure on a separable Banach space and $-1 \le \beta \le 1$. If
$u \sim \mu_0$ and $\xi \sim \mu_0$ are independent and $v = \sqrt{1 - \beta^2}\, u + \beta \xi$, then $(u, v)$
and $(v, u)$ have the same law.

Dashti and Stuart prove this on a separable Hilbert space by computing the covariance of the centred
Gaussian pair $(u, v)$: $\mathbb E\, u \otimes u = \mathbb E\, v \otimes v = C$ and
$\mathbb E\, u \otimes v = \sqrt{1 - \beta^2}\, C$. Another proof, valid on any separable Banach space, uses the rotation invariance of
$\mu_0 \otimes \mu_0$ (the key step in the proof of Fernique's theorem) with angle
$\theta = \arcsin \beta$: the map $(u, \xi) \mapsto (\sqrt{1-\beta^2}\, u + \beta \xi, \ \beta u - \sqrt{1-\beta^2}\, \xi)$ is
a reflection that preserves $\mu_0 \otimes \mu_0$ and exchanges $u$ and $v$.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Example 5.3 and the identities (5.3).
