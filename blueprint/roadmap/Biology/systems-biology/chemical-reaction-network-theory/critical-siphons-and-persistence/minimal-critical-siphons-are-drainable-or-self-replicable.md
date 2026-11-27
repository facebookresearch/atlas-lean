# Minimal critical siphons are drainable or self-replicable

**Setting.** A reaction network $G = (\mathscr{S},\mathscr{R})$ is *positive* if all complexes lie in $\mathbb{R}^{\mathscr{S}}_{\ge 0}$, and *consistent* if some strictly positive combination of reaction vectors vanishes. A *dilution* of $y \to y'$ by $w \ge 0$ is the reaction $y + w \to y' + w$, and a *reaction pathway* $y \Rightarrow_G y'$ is a finite sequence of dilutions of $G$-reactions. For $T \subseteq \mathscr{S}$:

- $T$ is a *siphon* if every reaction producing a species of $T$ consumes a species of $T$;
- $T$ is *critical* if no nonzero positive conservation law $w \cdot x$ ($w \ge 0$, $w \perp \operatorname{span}\{y'-y\}$) has support in $T$; equivalently $\ker \Gamma_T \cap \mathbb{R}^T_{\ge 0} = \{0\}$ for the stoichiometric submatrix $\Gamma_T$, equivalently some boundary point vanishing exactly on $T$ has a stoichiometric class meeting the open positive orthant;
- $T$ is *self-replicable* (autocatalytic) if some pathway $y \Rightarrow_G y'$ has $(y'-y)_i > 0$ for all $i \in T$, and *drainable* if some pathway has $(y'-y)_i < 0$ for all $i \in T$.

$G$ is *persistent* if for all positive rate constants and positive initial data, no omega-limit point of the mass-action ODE $\dot x = \sum k_{y\to y'}(y'-y)x^y$ lies on the boundary of the orthant.

**Theorem.** Let $G$ be a positive reaction network and $\emptyset \neq T \subseteq \mathscr{S}$.

1. If $T$ is drainable or self-replicable, then $T$ is critical.
2. If $T$ is a minimal critical siphon, then $T$ is drainable or self-replicable.
3. If $G$ is consistent, then $T$ is critical $\iff$ drainable $\iff$ self-replicable.
4. (Persistence.) If $G$ has no drainable siphons, then $G$ is persistent.
5. (Catalysis.) A self-replicable siphon is a strictly catalytic set, and every weakly reversible chemical network with a critical siphon is strictly catalytic (hence catalytic).

## Depends on

- [Is Siphon](../../../not-yet-classified/siphon-prime-decomposition/is-siphon.md)
- [Weakly reversible reaction network](../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Expansion

A positive conservation law supported in $T$ would be constant along every pathway, which is impossible if the pathway strictly increases (or strictly decreases) all species of $T$; this gives (1). For (2), the restricted stoichiometric matrix of a minimal critical siphon has a sign structure (a "strongly diffusive" matrix after suitable reduction), and a convex rank–nullity alternative for such matrices shows that either a nonnegative kernel vector exists (contradicting criticality) or the cone of rows contains a strictly positive or strictly negative vector, i.e. a self-replicating or draining pathway. Since omega-limit points on the boundary vanish on a siphon and solutions there can only approach siphons that can be drained, excluding drainable siphons yields persistence, refining the classical criterion that networks without critical siphons are persistent.

## Sources

- Abhishek Deshpande and Manoj Gopalkrishnan, "Autocatalysis in Reaction Networks", Bulletin of Mathematical Biology 76 (2014), 2570–2595, <https://doi.org/10.1007/s11538-014-0024-x>; numbering as in arXiv:1309.3957: Definitions 3.1 and 6.1, Theorems 3.7, 4.9, 5.3, 6.2, Corollary 7.11 and Theorem 7.13.
