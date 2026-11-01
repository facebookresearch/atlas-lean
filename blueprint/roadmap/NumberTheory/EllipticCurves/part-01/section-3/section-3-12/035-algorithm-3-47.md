---
article_id: af_6ee2a4cb6434129249e52ddd
declaration: def
origin: cited
statement: formalized
lean: BerlekampRabin.cantorZassenhausAlgorithm
---

# Algorithm 3.47

Given a monic polynomial $f \in \mathbb{F}_{q}[x]$, compute its irreducible factorization as follows:
1. Compute the squarefree factorization of $f=g_{1} g_{2}^{2} \cdots g_{m}^{m}$ using Yun's algorithm.
2. By successively computing $g_{ij}=\operatorname{gcd}\left(g_{i}, x^{q^{j}}-x\right)$ and replacing $g_{i}$ with $g_{i}/g_{ij}$ for $j=1,2,3, \ldots \operatorname{deg} g_{i}$, factor each $g_{i}$ into polynomials $g_{ij}$ that are each (possibly trivial) products of distinct irreducible polynomials of degree $j$; note that once $j>(\operatorname{deg} g_{i})/2$ we know $g_{i}$ must be irreducible and can immediately determine all the remaining $g_{ij}$.
3. Factor each nontrivial $g_{ij}$ into irreducible polynomials $g_{ijk}$ of degree $j$ as follows: while $\operatorname{deg} g_{ij}>j$ generate random polynomials $u \in \mathbb{F}_{q}[x]$ with $\operatorname{deg} u < \operatorname{deg} g_{ij}$ until either $h=\operatorname{gcd}\left(g_{ij}, u\right)$ or $h\coloneqq\operatorname{gcd}\left(g_{ij}, u^{(q^{j}-1)/2}-1\right)$ properly divides $g_{ij}$, then recursively factor $h$ and $g_{ij}/h$ (note that $j \mid \operatorname{deg} h$ and $j \mid \operatorname{deg}(g_{ij}/h)$).
4. Output each $g_{ijk}$ with multiplicity $i$.

## Depends on

- [Definition 3.4](../section-3-1/007-definition-3-4.md)
- [Algorithm 3.46](../section-3-11-2/034-algorithm-3-46.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.12](../../../../../../sources/v1/EllipticCurves.md)
