# Feinberg's characterization of the deficiency

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
$Y \colon \mathbb{R}^K \to \mathbb{R}^S$ be the linear map with $Y(e_c) = y(c)$. Then, computed in
the integers,

$$n - \ell - s = \dim (\ker Y \cap \Delta).$$

When $K$ is the set of [complexes](../../../Dynamics/smooth-dynamics/complexes.md) of $N$ and $y$
the inclusion, $G$ is the [linkage graph](../../../Dynamics/smooth-dynamics/linkage-graph.md) and
$n - \ell - s$ is the [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) $\delta$ of $N$,
so $\delta = \dim (\ker Y \cap \Delta)$.

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), Theorem 6.4.7.
- M. Feinberg, *Chemical reaction network structure and the stability of complex isothermal
  reactors I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 42 (1987)
  2229–2268, § 3.
