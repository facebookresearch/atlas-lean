# Copying $x$ into $y$ keeps low equivalence exactly when $\Gamma(x) \sqsubseteq \Gamma(y)$

Let security levels be preordered by $\sqsubseteq$, let $\Gamma : V \to \mathcal{L}$ be a
security policy, let $x, y \in V$, and let the set $A$ of values have at least two elements.
Copying $x$ into $y$, which maps a store $\sigma$ to $\sigma[y \mapsto \sigma(x)]$, maps stores
with $\sigma_1 =_\ell \sigma_2$ to stores with
$\sigma_1[y \mapsto \sigma_1(x)] =_\ell \sigma_2[y \mapsto \sigma_2(x)]$ for every observer level
$\ell$ if and only if $\Gamma(x) \sqsubseteq \Gamma(y)$.
