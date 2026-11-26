# Proximity gaps and correlated agreement for Reed–Solomon codes

Let $V = \mathrm{RS}[\mathbb{F}, D, k]$ be the Reed–Solomon code of dimension $k$ (polynomials of degree less than $k$) with rate $\rho = k/n$, $n = |D|$; the results below are Ben-Sasson et al., Theorem 1.5, with the error parameters of their Theorem 1.2 (the source indexes the code by its degree bound, so its $k+1$ is the $k$ here). (i) *Unique-decoding regime:* for words $u_0, \dots, u_{l-1}$ and $\delta < (1-\rho)/2$, if

$$
\Pr_{z \in \mathbb{F}}\Bigl[\Delta\bigl(\textstyle\sum_r z^r u_r, V\bigr) \le \delta\Bigr] > \frac{(l-1)\, n}{|\mathbb{F}|},
$$

then $u_0, \dots, u_{l-1}$ have *correlated agreement*: there is a set $S \subseteq D$ with $|S| \ge (1-\delta) n$ on which all $u_r$ agree with codewords. (ii) *Johnson regime:* the same conclusion holds for $\delta < 1 - \sqrt{\rho} - \eta$, for any $\eta > 0$, with the probability threshold replaced by $(l-1)\,k^2 / \bigl((2\min(\eta, \sqrt\rho/20))^7\,|\mathbb{F}|\bigr)$ (Guruswami–Sudan list decoding).

## Proof sketch

In the unique-decoding regime, the decoded codewords for different $z$ are interpolated by a polynomial of degree $l-1$ in $z$, which yields codewords for the $u_r$ agreeing on a common large set. In the Johnson regime, the Guruswami–Sudan algorithm over the rational function field in $z$ produces the same interpolating structure.

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Johnson bound](../../../../../InformationTheory/error-correcting-codes/list-decoding/johnson-bound.md)
- [List-decodable code](../../../../../InformationTheory/error-correcting-codes/list-decoding/is-list-decodable.md)

## Sources

- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
- Venkatesan Guruswami and Madhu Sudan, "Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes", IEEE Transactions on Information Theory, 1999.
