# Scaling a CRT-represented integer by $t/q$

With half-up rounding $\lfloor z\rceil=\lfloor z+\tfrac12\rfloor$, the residue modulo $t$ of $\lfloor\tfrac tq x\rceil$, for a centered residue $x$ modulo $q=q_1\cdots q_k$, is a rounded linear form in the residues $x_i$ with precomputed rational coefficients $t\tilde q_i/q_i$; no positional representation is needed.

Let $q=q_1\cdots q_k$ be an RNS base with $q_i^{*}=q/q_i$, and let $\tilde q_i\in[-q_i/2,q_i/2)$ be the centered inverse of $q_i^{*}$ modulo $q_i$. Fix the rounding $\lfloor z\rceil=\lfloor z+\tfrac12\rfloor$. Let $t\ge 2$ be an integer, let $x$ be an integer with $-q/2\le x<q/2$, and let $x_i=[x]_{q_i}$. Then

$$
\Bigl[\Bigl\lfloor\frac{t}{q}\,x\Bigr\rceil\Bigr]_t=\Bigl[\Bigl\lfloor\sum_{i=1}^{k}x_i\cdot\frac{t\,\tilde q_i}{q_i}\Bigr\rceil\Bigr]_t .
$$

Writing $t\tilde q_i/q_i=\omega_i+\theta_i$ with $\omega_i\in\mathbb{Z}$ and $\theta_i\in[-\tfrac12,\tfrac12)$, this equals $\bigl[\sum_ix_i\omega_i+\lfloor\sum_ix_i\theta_i\rceil\bigr]_t$: an integer inner product modulo $t$ plus one rounded real inner product of length $k$. Applied to each coefficient of $x=[c_0+c_1s]_q$ this is the decryption step of RNS BFV. If the $\theta_i$ and the sum are evaluated approximately and half-up rounding is then applied exactly to the computed sum, the result is still exact provided the total error of the computed value of $\sum_ix_i\theta_i$ (stored $\theta_i$, products and summation) is smaller than the distance of $\tfrac tq x$ to $\mathbb{Z}+\tfrac12$; in decryption the noise can be kept small enough that $\tfrac tq x$ is within $1/4$ of an integer, and then a total error below $1/4$ suffices.

## Depends on

- [Residue number system representation of $R_q$](rns-representation.md)

## Proof depends on

None.

## Expansion

HPS §2.1, Eq. (3), and §2.3, Eq. (4): $x=\sum_ix_i\tilde q_iq_i^{*}-\upsilon' q$ for an integer $\upsilon'$, so $\tfrac tq x=\sum_ix_it\tilde q_i/q_i-\upsilon' t$. A rounding of the form $\lfloor z+\tfrac12\rfloor$ commutes with adding an integer, so the integer $\upsilon' t$ passes through the rounding and vanishes modulo $t$; the same holds for the integer parts $\omega_i$. A rounding rule that depends on parity, such as ties to even, does not commute with integer translation and can change the residue at ties.

## Sources

- Shai Halevi, Yuriy Polyakov, Victor Shoup, "An Improved RNS Variant of the BFV Homomorphic Encryption Scheme", Topics in Cryptology – CT-RSA 2019, LNCS 11405 (2019), pp. 83–105, DOI [10.1007/978-3-030-12612-4_5](https://doi.org/10.1007/978-3-030-12612-4_5): §2 (centered conventions, Eq. (1)), §2.1, Eq. (3), §2.3, Eq. (4) and its "Correctness" paragraph, and §4.4 (decryption); authors' version of December 5, 2018.
