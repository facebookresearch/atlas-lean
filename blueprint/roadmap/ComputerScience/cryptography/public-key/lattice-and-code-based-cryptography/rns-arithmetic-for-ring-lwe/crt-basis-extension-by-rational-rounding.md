# CRT basis extension by rounding the rational overflow

The overflow of the CRT reconstruction sum is the nearest integer to $\sum_i y_i/q_i$, where $y_i=[x_i\tilde q_i]_{q_i}$; computing it removes the $q$-overflow and extends a centered residue $x\in[-q/2,q/2)$ exactly to any new modulus.

Let $q=q_1\cdots q_k$ be an RNS base with $q_i^{*}=q/q_i$ and $\tilde q_i\equiv(q_i^{*})^{-1}\pmod{q_i}$, and write $[\cdot]_m$ for the centered residue in $[-m/2,m/2)$. Let $x$ be an integer with $-q/2\le x<q/2$ and residues $x_i=[x]_{q_i}$, and put $y_i=[x_i\tilde q_i]_{q_i}$. Then

$$
x=\sum_{i=1}^{k}y_iq_i^{*}-\upsilon q,\qquad \upsilon=\Bigl\lfloor\frac12+\sum_{i=1}^{k}\frac{y_i}{q_i}\Bigr\rfloor ,
$$

so for every modulus $p\ge 2$,

$$
[x]_p=\Bigl[\sum_{i=1}^{k}y_i\,[q_i^{*}]_p-\upsilon\,[q]_p\Bigr]_p .
$$

With word-size moduli $p,q_i$ and the constants $[q_i^{*}]_p$, $[q]_p$ precomputed, the procedure uses $k$ word multiplications for the $y_i$, $k$ floating-point divisions and one rounding for $\upsilon$, and $k+1$ word multiplications for the inner product. The identity is exact when $\upsilon$ is computed exactly. With floating-point arithmetic and half-up rounding applied exactly to the computed sum, the computed $\upsilon$ is still correct provided the total error of the computed sum (divisions, representation and summation) is smaller than the distance of $\sum_iy_i/q_i$ to $\mathbb{Z}+\tfrac12$; since $\sum_iy_i/q_i\equiv x/q\pmod 1$, this holds when $|x|<q/4$ and the total error is at most $1/4$.

## Depends on

- [Residue number system representation of $R_q$](rns-representation.md)

## Proof depends on

None.

## Expansion

HPS §2.1–2.2: the sum $\sum_iy_iq_i^{*}$ is congruent to $x$ modulo $q$, so it equals $x+\upsilon q$ for an integer $\upsilon$, and dividing by $q$ gives $\sum_iy_i/q_i=x/q+\upsilon$ with $x/q\in[-\tfrac12,\tfrac12)$, whence $\upsilon=\lfloor\tfrac12+\sum_iy_i/q_i\rfloor$. Reducing modulo $p$ gives the extension. HPS check the computed value against the error region $\mathbb{Z}+\tfrac12\pm\varepsilon$ and observe that inputs with $|x|\ll q$ never fall into it.

## Sources

- Shai Halevi, Yuriy Polyakov, Victor Shoup, "An Improved RNS Variant of the BFV Homomorphic Encryption Scheme", Topics in Cryptology – CT-RSA 2019, LNCS 11405 (2019), pp. 83–105, DOI [10.1007/978-3-030-12612-4_5](https://doi.org/10.1007/978-3-030-12612-4_5): §2 (centered conventions, Eq. (1)), §2.1, Eq. (2), and §2.2 (procedure, complexity analysis and "Correctness" paragraph); authors' version of December 5, 2018.
