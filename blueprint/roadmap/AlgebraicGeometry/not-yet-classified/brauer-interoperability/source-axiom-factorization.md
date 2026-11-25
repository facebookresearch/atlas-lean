# Source axiom factorization

For a field $K$ such that the category of discrete modules over its absolute Galois group
$G_K$ has enough injectives, and an isomorphism
$B : H^2_{\mathrm{et}}(\operatorname{Spec} K, \mathbb{G}_m) \cong \mathrm{Br}(K)$ normalized on
the Čech classes of two-cocycles (`FieldGmComparison`): a factorization of $B$ through the derived
functors of $G_K$-invariants (`AxiomFieldFactorization`), that is, for every $n$, isomorphisms of
abelian groups from $H^n_{\mathrm{et}}(\operatorname{Spec} K, \mathbb{G}_m)$ to the degree-$n$
cohomology of the total right derived functor of $G_K$-invariants on the bounded below derived
category, applied to $(K^{\mathrm{sep}})^\times$ (`etale`), and from the latter to the continuous
cohomology $H^n(G_K, (K^{\mathrm{sep}})^\times)$ (`continuous`), whose composite sends, in degree
zero, the class of each unit $u \in K^\times$ to
$u \in ((K^{\mathrm{sep}})^\times)^{G_K} = H^0(G_K, (K^{\mathrm{sep}})^\times)$ (`zero_units`),
and is $B$ in degree two (`two_agrees`).
