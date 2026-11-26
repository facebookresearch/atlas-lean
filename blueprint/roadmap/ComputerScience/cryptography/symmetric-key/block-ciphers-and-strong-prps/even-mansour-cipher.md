# Even–Mansour block cipher

Given a public permutation $P$ of $\{0,1\}^n$, the *Even–Mansour* cipher with key $(k_1, k_2)$ is

$$E_{k_1,k_2}(x) = P(x \oplus k_1) \oplus k_2, \qquad D_{k_1,k_2}(y) = P^{-1}(y \oplus k_2) \oplus k_1.$$

The *single-key* variant uses $k_1 = k_2 = k$.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)

## Sources

- S. Even and Y. Mansour, "A Construction of a Cipher from a Single Pseudorandom Permutation", Journal of Cryptology 10(3), 1997.
- O. Dunkelman, N. Keller and A. Shamir, "Minimalism in Cryptography: The Even-Mansour Scheme Revisited", Advances in Cryptology (EUROCRYPT 2012), LNCS 7237, 2012.
