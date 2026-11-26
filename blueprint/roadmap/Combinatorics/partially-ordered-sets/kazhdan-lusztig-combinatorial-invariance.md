# Combinatorial invariance of equal-parameter Kazhdan–Lusztig polynomials

For arbitrary Coxeter systems, let $u\le b$ and $u'\le b'$ in their strong Bruhat orders (the reflexive transitive closure of length-increasing left multiplication by a reflection). Any isomorphism of the unlabelled closed interval posets $[u,b]\cong[u',b']$ gives $P_{u,b}(q)=P_{u',b'}(q)$ in $\mathbb Z[q]$.

Here $R_{x,x}=P_{x,x}=1$ and both families vanish off comparable pairs. If $s$ is a simple left descent of $y$, then $R_{x,y}=R_{sx,sy}$ if $s$ is a left descent of $x$, and otherwise $R_{x,y}=(q-1)R_{x,sy}+qR_{sx,sy}$. For $x<y$ use $2\deg P_{x,y}<\ell(y)-\ell(x)$ and $q^{\ell(y)-\ell(x)}P_{x,y}(q^{-1})=\sum_{x\le z\le y}R_{x,z}(q)P_{z,y}(q)$. The source selects families by this normalization, with coefficient reflection and a finite-support sum.

## Depends on

- Strong Bruhat intervals and existence and uniqueness for the equal-parameter normalization.

## Proof depends on

- Reconstruction of the normalized polynomial from the unlabelled order, not from a chosen edge labeling.

## Expansion

Connect the selected polynomial families to the defining recursion and the interval finiteness theorem. Isolate the poset-invariant comparison and account for singleton intervals.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KLInvariance.lean#L88-L96) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KLInvariance.lean).
