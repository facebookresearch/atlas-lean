---
article_id: af_0d06e32177ef93442f210c9b
declaration: theorem
origin: cited
lean: AlgebraicTopologyI.crossProduct_exists
---

# Theorem 6.2

There exists a map $\times \colon S_{p}(X) \times S_{q}(Y) \rightarrow S_{p+q}(X \times Y)$, the cross product, that is: Natural, in the sense that if $f \colon X \rightarrow X'$ and $g \colon Y \rightarrow Y'$, and $a \in S_{p}(X)$ and $b \in S_{q}(Y)$ so that $a \times b \in S_{p+q}(X \times Y)$, then $f_{*}(a) \times g_{*}(b) = (f \times g)_{*}(a \times b)$. Bilinear, in the sense that $(a + a') \times b = (a \times b) + (a' \times b)$, and $a \times (b + b') = a \times b + a \times b'$. The Leibniz rule is satisfied, i.e., $d(a \times b) = (da) \times b + (-1)^{p} a \times db$. Normalized, in the following sense: Let $x \in X$ and $y \in Y$. Write $j_{x} \colon Y \rightarrow X \times Y$ for $y \mapsto (x,y)$, and write $i_{y} \colon X \rightarrow X \times Y$ for $x \mapsto (x,y)$. If $b \in S_{q}(Y)$, then $c_{x}^{0} \times b = (j_{x})_{*} b \in S_{q}(X \times Y)$, and if $a \in S_{p}(X)$, then $a \times c_{y}^{0} = (i_{y})_{*} a \in S_{p}(X \times Y)$.

## Depends on

- [Definition 1.3](../chapter-1-section-1/003-definition-1-3.md)

## Proof depends on

- [Definition 1.2](../chapter-1-section-1/002-definition-1-2.md)
- [Theorem 1.5](../chapter-1-section-1/005-theorem-1-5.md)
- [Definition 5.12](../chapter-1-section-5/028-definition-5-12.md)
- [Proposition 5.13](../chapter-1-section-5/029-proposition-5-13.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Chapter 1, Section 6](../../../../../../sources/v1/AlgebraicTopologyI.md)
