# Inverse theorem for the $U^3$ norm over $\mathbb{F}_5^n$

Let $f : \mathbb{F}_5^n \to \mathbb{C}$ be bounded by $1$ and let $0 < \eta \le 1$ with $\|f\|_{U^3} \ge \eta$. Then there are a subspace $W$ of codimension at most $(2/\eta)^C$, a point $y$ and a function $\varphi : \mathbb{F}_5^n \to \mathbb{R}/\mathbb{Z}$ whose third differences $(h_1 \cdot \nabla)(h_2 \cdot \nabla)(h_3 \cdot \nabla)\varphi(x)$ vanish whenever $x \in y + W$ and $h_1, h_2, h_3 \in W$ (a quadratic phase locally on $y + W$), such that

$$\bigl|\mathbb{E}_{x \in y + W} f(x)\, e(-\varphi(x))\bigr| \ge (\eta/2)^C, \qquad C = 2^{16}.$$

This is the "in particular" form of Theorem 2.3(i) of Green and Tao, whose conclusion is $\|f\|_{u^3(y + W)} \ge (\eta/2)^C$ for the local quadratic bias of their Definition 2.1; that supremum is attained by compactness, so the two forms are equivalent. A cube $(x + \omega \cdot h)_{\omega \in \{0,1\}^3}$ lies in $y + W$ exactly when $x \in y + W$ and $h_1, h_2, h_3 \in W$.

For $U^2$ the corresponding statement needs only characters ([$U^2$ inverse theorem](exists-character-correlation-of-le-gower.md)); for $U^3$ quadratic phases are necessary, because $\|e(q)\|_{U^3} = 1$ for every quadratic $q$ while $e(q)$ need not correlate with any character. Over $\mathbb{Z}_N$ even global quadratic phases do not suffice (Green and Tao, Example 2.4), which is why their Theorem 2.7 uses Bohr sets.

## Background

- [Gowers's bound for Szemerédi's theorem](szemeredi-gowers-bound.md): Gowers's proof rests on a weaker inverse theorem for every $U^k$, obtained with the same tools.
- [Balog–Szemerédi–Gowers theorem](../../sumsets-inverse-theorems/freiman-and-balog-szemer-di-gowers-theorems/balog-szemeredi-gowers.md): background rather than a prerequisite, since the linked statement is Gowers's version for $\mathbb{Z}^n$, while Green and Tao use the version of their Theorem 5.2 (stated for arbitrary additive groups, with different constants).

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Theorem 2.3 and Definition 2.1.
