# Linearity, multiplicativity and privacy of Shamir sharing

For Shamir sharing with threshold $t$ over $\mathbb{F}$: (i) *linearity*: shares of $z + z'$ (with randomness $r + r'$) are the sums of shares, shares of $cz$ are $c$ times the shares, and reconstruction is the linear functional $\sum_{i\in S}\lambda_i^S \sigma_i$; more generally for any set $L$ of at least $t$ parties, every party's share is a fixed linear combination of the secret and the shares of $L$; (ii) *multiplicativity*: the pointwise products of shares of $a$ and $b$ are evaluations of a degree-$2t$ polynomial with constant term $ab$, so when $2t < m$ Lagrange reconstruction from all products returns $ab$; (iii) *privacy*: for every coalition $I$ with $|I| \le t$ and every secret, the shares of $I$ are uniform on $\mathbb{F}^I$, and for a vector of secrets shared with independent randomness the joint view of $I$ is uniform on $(\mathbb{F}^I)^{\kappa}$.

## Proof sketch

(i) and (ii) follow from linearity of evaluation and of Lagrange interpolation. For (iii), given target shares $\sigma \in \mathbb{F}^I$, Lagrange interpolation through the $|I| + 1 \le t + 1$ points $(0, z)$ and $(\alpha_i, \sigma_i)$ gives a tail polynomial of degree at most $t$, so the restriction map from randomness to shares of the zero secret is a surjective group homomorphism, which pushes the uniform distribution to the uniform distribution.

## Depends on

- [Shamir threshold secret sharing](shamir-secret-sharing.md)

## Sources

- Adi Shamir, "How to Share a Secret", Communications of the ACM, 1979.
- Michael Ben-Or, Shafi Goldwasser and Avi Wigderson, "Completeness Theorems for Non-Cryptographic Fault-Tolerant Distributed Computation", Proceedings of the Twentieth Annual ACM Symposium on Theory of Computing, 1988.
- Gilad Asharov and Yehuda Lindell, "A Full Proof of the BGW Protocol for Perfectly Secure Multiparty Computation", Journal of Cryptology, 2017.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
