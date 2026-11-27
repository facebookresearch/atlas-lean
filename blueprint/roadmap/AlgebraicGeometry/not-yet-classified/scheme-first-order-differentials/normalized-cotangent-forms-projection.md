# A cotangent complex with a projection to Kähler one-forms

Assume that derived pullbacks,
pushforwards and tensor products exist (`HasDerivedPullbacks`, `HasDerivedPushforwards`,
`HasDerivedTensors`). For a commutative ring $k$ and a $k$-scheme $U$: a cotangent normalization $P$
of $U \to \operatorname{Spec} k$ (a complex of $\mathcal{O}_U$-modules with, on every affine chart,
a polynomial resolution and a quasi-isomorphism from its cotangent complex to the sections of $P$,
compatible with refinements of charts), together with a map from $P$ to $\Omega^1_{U/k}$ placed in
degree $0$ that sends, on every affine chart, the degree-zero cotangent differential of each element
$x$ of the resolution to the Kähler differential of the image of $x$. Such a projection need not
exist for an arbitrary representative of the cotangent complex: on $\operatorname{Spec} k[t]$ the
quasi-isomorphic model $[k[t] \to k[t]/(t)]$ (degrees $0$ and $1$, receiving $dt \mapsto t$) has no
$k[t]$-linear map back sending $t$ to $dt$.
