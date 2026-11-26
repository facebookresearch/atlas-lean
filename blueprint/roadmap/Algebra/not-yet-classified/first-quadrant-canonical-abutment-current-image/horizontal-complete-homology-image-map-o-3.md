# Horizontal Complete Homology Image Map Of Bicomplex eq current

Let $C$ be an abelian category, let $K,L$ be double chain complexes in $C$
indexed by $\mathbb N$ in both directions, and let $f:K\to L$ be a bicomplex
map. For every $p,q\in\mathbb N$, the map induced by $f$ on complete-stage
homology images, at total degree $p+q$ and the first-page upper filtration
index for $p$, equals the corresponding total-homology filtration map:

```lean
horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
    (horizontalFirstPageUpperIndex p) =
  horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q
```
