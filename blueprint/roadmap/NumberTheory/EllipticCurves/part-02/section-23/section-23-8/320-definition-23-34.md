---
article_id: af_e44263b91cf0cee74d8f8c59
declaration: def
origin: cited
lean: WeilPairing.tatePairing
---

# Definition 23.34

Let $n>2$ be an integer and let $E / \mathbb{F}_{q}$ be an elliptic curve
 over a finite field with embedding degree $k$ with respect to $n$. The
 (modified) Tate pairing is the map $t_{n}: E[n] \times E[n] \rightarrow
 \mu_{n}$ defined by $t_{n}(P, Q)\coloneqq\left(\frac{f_{n, P}(Q+T)}{f_{n,
 P}(T)}\right)^{(q^{k}-1)/n}$ where $T \in E[n]-\{0, P,-Q, P-Q\}$.

## Depends on

- [Definition 23.32](../section-23-7/318-definition-23-32.md)
- [Definition 3.4](../../../part-01/section-3/section-3-1/007-definition-3-4.md)

## Proof depends on

- [Definition 23.23](../section-23-5/310-definition-23-23.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 23.8](../../../../../../sources/v1/EllipticCurves.md)
