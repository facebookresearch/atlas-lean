# Residue number system representation of $R_q$

For pairwise coprime moduli $q_1,\dots,q_k$ with product $q$, the Chinese remainder theorem identifies $R_q=\mathbb{Z}_q[X]/(X^n+1)$ with $R_{q_1}\times\cdots\times R_{q_k}$ coefficientwise, so additions and multiplications modulo $q$ run independently on the residues.

Let $q_1,\dots,q_k$ be pairwise coprime integers, each at least $2$. The list $\{q_1,\dots,q_k\}$ is the *RNS base*, and $q=\prod_{i=1}^{k}q_i$ is its product. Write $q_i^{*}=q/q_i$ and let $\tilde q_i$ be an inverse of $q_i^{*}$ modulo $q_i$. For an integer $m\ge 2$ write $|x|_m\in[0,m)$ and $[x]_m\in[-m/2,m/2)$ for the residues of $x$ modulo $m$. The *RNS representation* of $x\in\mathbb{Z}_q$ is $(x_1,\dots,x_k)$ with $x_i=x\bmod q_i$. The map

$$
\mathbb{Z}_q\longrightarrow\mathbb{Z}_{q_1}\times\cdots\times\mathbb{Z}_{q_k},\qquad x\longmapsto(x\bmod q_1,\dots,x\bmod q_k)
$$

is a ring isomorphism, with inverse given by

$$
x\equiv\sum_{i=1}^{k}x_i\,\tilde q_i\,q_i^{*}\pmod q .
$$

Applied to each coefficient, it gives a ring isomorphism $R_q\cong R_{q_1}\times\cdots\times R_{q_k}$, where $R_m=\mathbb{Z}_m[X]/(X^n+1)$, so additions and multiplications in $R_q$ are computed componentwise in the $R_{q_i}$. Operations that are not ring operations modulo $q$, such as rounding $\tfrac{t}{q}x$ or lifting $x$ to a larger modulus, cannot in general be computed separately in each $R_{q_i}$.

## Depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](../lattice-problems/negacyclic-ring.md)

## Proof depends on

- [Chinese remainder theorem as an algebra isomorphism](../../../../../RingTheory/ideals-and-constructions/chinese-remainder-theorem-for-polynomial-quotien/quotient-inf-alg-equiv-pi-quotient.md)

## Expansion

The integer statement is the Chinese remainder theorem for the pairwise coprime ideals $q_i\mathbb{Z}$ of the $\mathbb{Z}$-algebra $\mathbb{Z}$, whose intersection is $q\mathbb{Z}$; the reconstruction formula holds because $\tilde q_iq_i^{*}\equiv 1\pmod{q_i}$ and $q_i^{*}\equiv 0\pmod{q_j}$ for $j\ne i$. The polynomial statement follows coefficientwise, since reduction modulo $q_i$ commutes with multiplication modulo $X^n+1$.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §2, paragraph "RNS representation"; authors' version.
- Shai Halevi, Yuriy Polyakov, Victor Shoup, "An Improved RNS Variant of the BFV Homomorphic Encryption Scheme", Topics in Cryptology – CT-RSA 2019, LNCS 11405 (2019), pp. 83–105, DOI [10.1007/978-3-030-12612-4_5](https://doi.org/10.1007/978-3-030-12612-4_5): §2, Eq. (1), and §2.1 (reconstruction formula); authors' version of December 5, 2018.
- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §2.2 (the RNS ring isomorphism on $\mathbb{Z}_P$ and on the cyclotomic ring); read as the author manuscript PMC8048025.
