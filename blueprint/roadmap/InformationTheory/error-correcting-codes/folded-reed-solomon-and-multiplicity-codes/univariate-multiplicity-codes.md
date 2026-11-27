# Univariate multiplicity codes

Let $p \ge k$ be a prime and $\alpha_1, \dots, \alpha_n \in \mathbb{F}_p$ distinct. The *univariate multiplicity code* of order $s$ maps $f \in \mathbb{F}_p[x]$ with $\deg f < k$ to

$$
\Big( \big(f(\alpha_i), f'(\alpha_i), \dots, f^{(s-1)}(\alpha_i)\big) \Big)_{i=1}^{n} \in (\mathbb{F}_p^{s})^{n},
$$

with rate $R = k/(sn)$ and requiring $k \le sn$. Its relative distance is at least $1 - R$, since a nonzero polynomial of degree $< k$ has at most $(k-1)/s$ roots of multiplicity at least $s$.

## Depends on

- [Reed-Solomon code](../reed-solomon-codes/code.md)
- [Root of multiplicity $r$](../list-decoding/has-root-mult.md)

## Sources

- Swastik Kopparty, Shubhangi Saraf, Sergey Yekhanin, "High-rate codes with sublinear-time decoding", Journal of the ACM 61(5) (2014).
- Swastik Kopparty, "List-decoding multiplicity codes", Theory of Computing 11 (2015).
