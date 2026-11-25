# Deficiency zero criterion for indexed complexes

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and finite reaction set $\rho$. Index complexes by a finite set $K$: let
$y \colon K \to \mathbb{N}^S$ and $\sigma, \tau \colon \rho \to K$ satisfy
$\mathrm{src}(r) = y(\sigma(r))$ and $\mathrm{prod}(r) = y(\tau(r))$ for every reaction $r$. Let $G$
be the simple graph on $K$ in which distinct $c, c'$ are adjacent exactly when some reaction $r$ has
$(\sigma(r), \tau(r)) = (c, c')$ or $(\sigma(r), \tau(r)) = (c', c)$, and let $\ell$ be its number
of connected components. Write $n = |K|$ and $s$ for the dimension of the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md) of $N$, let
$\Delta \subseteq \mathbb{R}^K$ be the span of the incidence vectors $e_{\tau(r)} - e_{\sigma(r)}$,
$r \in \rho$, where $(e_c)_{c \in K}$ is the standard basis of $\mathbb{R}^K$, and let
$Y \colon \mathbb{R}^K \to \mathbb{R}^S$ be the linear map with $Y(e_c) = y(c)$. Then
$n - \ell - s = 0$, computed in the integers, if and only if $\ker Y \cap \Delta = \{0\}$, that is,
if and only if $Y$ is injective on $\Delta$.

When $K$ is the set of [complexes](../../../Dynamics/smooth-dynamics/complexes.md) of $N$ and $y$
the inclusion, $G$ is the [linkage graph](../../../Dynamics/smooth-dynamics/linkage-graph.md) and
$n - \ell - s$ is the [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) $\delta$ of $N$,
so $\delta = 0$ exactly when $\ker Y \cap \Delta = \{0\}$.

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), § 6.4.
