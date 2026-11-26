# Proximity gaps and correlated agreement for Reed–Solomon codes

Let $V = \mathrm{RS}[\mathbb{F}, D, k]$ with rate $\rho = k/n$, $n = |D|$. (i) *Unique-decoding regime:* for words $u_0, \dots, u_{l-1}$ and $\delta < (1-\rho)/2$, if

$$
\Pr_{z \in \mathbb{F}}\Bigl[\Delta\bigl(\textstyle\sum_r z^r u_r, V\bigr) \le \delta\Bigr] > \frac{(l-1)\, n}{|\mathbb{F}|},
$$

then $u_0, \dots, u_{l-1}$ have *correlated agreement*: there is a set $S \subseteq D$ with $|S| \ge (1-\delta) n$ on which all $u_r$ agree with codewords. (ii) *Johnson regime:* the same conclusion holds for $\delta < 1 - \sqrt{\rho} - \eta$, with the probability threshold replaced by a bound of order $(l-1)\, n^2 / (|\mathbb{F}|\, \eta^{O(1)})$ (Guruswami–Sudan list decoding). Integer-weighted variants give the corresponding statements for coset folding with arity $a$: if the fold $\mathrm{Fold}(f, z)$ is $\delta$-close to $\mathrm{RS}$ for too many $z$, then $f$ is $\delta$-close to $\mathrm{RS}$ of dimension $ak$ with correlated agreement of its fiber components.

## Proof sketch

In the unique-decoding regime, the decoded codewords for different $z$ are interpolated by a polynomial of degree $l-1$ in $z$, which yields codewords for the $u_r$ agreeing on a common large set. In the Johnson regime, the Guruswami–Sudan algorithm over the rational function field in $z$ produces the same interpolating structure.

## Depends on

- [Reed-Solomon code](../../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Johnson bound](../../../../../InformationTheory/error-correcting-codes/list-decoding/johnson-bound.md)
- [List-decodable code](../../../../../InformationTheory/error-correcting-codes/list-decoding/is-list-decodable.md)

## Sources

- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
- Venkatesan Guruswami and Madhu Sudan, "Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes", IEEE Transactions on Information Theory, 1999.
