# Scaling by $t/q$ into the complementary CRT base

For an integer $x\in[-qp/(2t),qp/(2t))$ known modulo $qp$, the residue of $\lfloor\tfrac tq x\rceil$ modulo each factor $p_j$ of $p$ is one rounded rational inner product over the $q$-residues plus one term in the $p_j$-residue. This is the first step of the scaling in RNS BFV multiplication.

Let $q=q_1\cdots q_k$ and $p=p_1\cdots p_{k'}$ be RNS bases with all moduli pairwise coprime. Put $Q=qp$, $Q_i^{*}=Q/q_i$, $Q_j'^{*}=Q/p_j$ and $p_j^{*}=p/p_j$, and let $\tilde Q_i$, $\tilde Q_j'$ be the centered inverses of $Q_i^{*}$ modulo $q_i$ and of $Q_j'^{*}$ modulo $p_j$. Fix the rounding $\lfloor z\rceil=\lfloor z+\tfrac12\rfloor$. Let $t\ge 2$ be the plaintext modulus and let $x$ be an integer with $-qp/(2t)\le x<qp/(2t)$ and residues $x_i=[x]_{q_i}$ and $x'_j=[x]_{p_j}$. Then for every $j$,

$$
\Bigl\lfloor\frac{t}{q}\,x\Bigr\rceil\equiv\Bigl\lfloor\sum_{i=1}^{k}x_i\cdot\frac{t\,\tilde Q_i\,p}{q_i}\Bigr\rceil+x'_j\,\bigl[t\,\tilde Q_j'\,p_j^{*}\bigr]_{p_j}\pmod{p_j}.
$$

If moreover $p$ is odd, then $\lfloor\tfrac tq x\rceil\in[-(p-1)/2,(p-1)/2]$, so the residues modulo the $p_j$ determine it; the CRT basis extension from $p$ to $q$ applied to this centered value then yields $[\lfloor\tfrac tq x\rceil]_q$, which completes the scaling. These statements concern exact arithmetic; HPS evaluate the rounded sum in floating point and analyze that separately.

## Depends on

- [Residue number system representation of $R_q$](rns-representation.md)
- [CRT basis extension by rounding the rational overflow](crt-basis-extension-by-rational-rounding.md)

## Proof depends on

None.

## Expansion

HPS §2.4: by the reconstruction identity in the joint base, $x=\sum_ix_i\tilde Q_iQ_i^{*}+\sum_jx'_j\tilde Q_j'Q_j'^{*}-\upsilon' Q$ for an integer $\upsilon'$. Multiplying by $t/q$, and using $Q_i^{*}/q=p/q_i$ and $Q_j'^{*}/q=p_j^{*}$, the second sum and the term $t\upsilon' p$ are integers, so they pass through the half-up rounding; modulo $p_j$ every $p_{j'}^{*}$ with $j'\ne j$ and the term $t\upsilon' p$ vanish. For odd $p$, a real $z\in[-p/2,p/2)$ has $\lfloor z+\tfrac12\rfloor\in[-(p-1)/2,(p-1)/2]$, a complete residue system modulo $p$.

## Sources

- Shai Halevi, Yuriy Polyakov, Victor Shoup, "An Improved RNS Variant of the BFV Homomorphic Encryption Scheme", Topics in Cryptology – CT-RSA 2019, LNCS 11405 (2019), pp. 83–105, DOI [10.1007/978-3-030-12612-4_5](https://doi.org/10.1007/978-3-030-12612-4_5): §2 (centered conventions), §2.4 (complex scaling, input range $[-qp/2t,qp/2t)$, displayed derivation and "Correctness" paragraph) and §4.5 (homomorphic multiplication); authors' version of December 5, 2018.
