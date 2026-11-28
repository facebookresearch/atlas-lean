# Counting subgroups of prime-power order in the torsion of an elliptic curve

For $\ell$ prime to the characteristic, an elliptic curve has $1+\ell+\cdots+\ell^m$ subgroups of order $\ell^m$, of which $\ell^m+\ell^{m-1}$ are cyclic. So it has that many separable, and cyclic, $\ell^m$-isogenies up to isomorphism of the target.

Let $E$ be an elliptic curve over a field $k$, $\ell$ a prime different from $\operatorname{char}k$, and $m\ge 1$. Every subgroup of $E(\bar k)$ of order $\ell^m$ lies in $E[\ell^m]$, and

$$
\#\{H\le E(\bar k):\#H=\ell^m\}=\frac{\ell^{m+1}-1}{\ell-1},\qquad \#\{H\le E(\bar k):H\cong\mathbb{Z}/\ell^m\mathbb{Z}\}=\ell^m+\ell^{m-1}.
$$

Equivalently, up to post-composition with an isomorphism of the target, $E$ has $(\ell^{m+1}-1)/(\ell-1)$ separable isogenies of degree $\ell^m$ defined over $\bar k$, of which $\ell^m+\ell^{m-1}$ are [cyclic](cyclic-isogeny.md); these are geometric counts, and over $k$ itself fewer subgroups may be defined. For $m=1$ both counts are $\ell+1$. The cyclic count is the value $\psi(\ell^m)=\ell^{m-1}(\ell+1)$ of the [Dedekind psi function](../../../NumberTheory/arithmetic-functions/divisor-totient-functions/part-01/dedekind-psi-function/dedekind-psi.md).

## Depends on

- [Cyclic isogeny](cyclic-isogeny.md)
- [Structure of the prime-power torsion of an elliptic curve](../isogenies-of-elliptic-curves/structure-of-prime-power-torsion.md)
- [Dedekind psi function](../../../NumberTheory/arithmetic-functions/divisor-totient-functions/part-01/dedekind-psi-function/dedekind-psi.md)

## Proof depends on

- [Dedekind psi function at prime powers](../../../NumberTheory/arithmetic-functions/divisor-totient-functions/part-01/dedekind-psi-function/dedekind-psi-prime-pow.md)
- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [The kernel of a nonzero isogeny has order its separable degree](../isogenies-of-elliptic-curves/kernel-order-equals-separable-degree.md)
- [Invariant factor decomposition of finite abelian groups](../../../GroupTheory/abelian-groups/structure-of-finitely-generated-abelian-groups/equiv-direct-sum-invariant-factors-of-fi.md)

## Expansion

Since $E[\ell^m]\cong(\mathbb{Z}/\ell^m\mathbb{Z})^2$, the counts are group theory. A cyclic subgroup of order $\ell^m$ contains $\ell^m-\ell^{m-1}$ generators, and $(\mathbb{Z}/\ell^m)^2$ has $\ell^m(\ell^m-\ell^{m-1})+\ell^{m-1}(\ell^m-\ell^{m-1})$ elements of order $\ell^m$, giving $\ell^m+\ell^{m-1}$ cyclic subgroups. Every subgroup of order $\ell^m$ is isomorphic to $\mathbb{Z}/\ell^i\oplus\mathbb{Z}/\ell^j$ with $i\le j$, $i+j=m$; there is one such subgroup when $i=j$ and $\ell^{j-i}+\ell^{j-i-1}$ otherwise, and summing over $i$ gives $1+\ell+\cdots+\ell^m$, the degree $\sigma_1(\ell^m)$ of the Hecke operator $T_{\ell^m}$. The isogeny form follows because separable isogenies correspond to their kernels. A good expansion adds a group-theory page for these counts in $\mathbb{Z}/\ell^m\oplus\mathbb{Z}/\ell^m$. (The proof of Lemma 4.6 in the source defines its parity correction through "$k$ odd" where $m$ is meant; the statement is unaffected.)

## Sources

- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Lemma 4.6, Remark 4.7 and Corollary 4.8.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Section 25.1, the paragraph before Exercise 25.1.1 ($\ell+1$ subgroups of order $\ell$).
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 2.2.
