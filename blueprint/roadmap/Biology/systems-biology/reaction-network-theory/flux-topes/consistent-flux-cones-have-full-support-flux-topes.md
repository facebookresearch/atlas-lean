# Consistent flux cones have only full-support flux topes

**Setting.** A metabolic network has stoichiometric matrix $N \in \mathbb{R}^{m \times r}$ and a
split of the reaction indices $\{1,\dots,r\}$ into irreversible reactions $I_{\mathrm{irr}}$ and
reversible reactions $I_{\mathrm{rev}}$. The **flux cone** is

$$C = \{ v \in \mathbb{R}^r : N v = 0,\ v_i \ge 0 \text{ for } i \in I_{\mathrm{irr}} \}.$$

Sign vectors $\{-,0,+\}^r$ are partially ordered componentwise by $0 < -$ and $0 < +$ (with $-$ and
$+$ incomparable). Let $\operatorname{sign}(C) = \{\operatorname{sign}(v) : v \in C\}$. For a
**maximal** element $\tau$ of $\operatorname{sign}(C)$, the pointed subcone

$$C_{\le \tau} = \{ v \in C : \operatorname{sign}(v) \le \tau \}$$

is a **flux tope** (FT): the set of all steady-state fluxes that use every reaction in a fixed
direction (or not at all). Elementary flux modes conforming to $\tau$ are exactly the extreme rays of
$C_{\le\tau}$. The cone $C$ is **consistent** if for every $i$ there is $v \in C$ with $v_i > 0$, and
for every $i \in I_{\mathrm{rev}}$ there is also $v' \in C$ with $v'_i < 0$.

**Proposition 1.** If $C$ is consistent, every reaction in every admissible direction is used by a
flux mode $v \in C$ with full support ($v_j \ne 0$ for all $j$).

**Proposition 2.** If $C$ is consistent, every flux tope has full support: each maximal sign vector
$\tau \in \operatorname{sign}(C)$ lies in $\{-,+\}^r$.

## Expansion

Both proofs are a convex-combination argument. If $v \in C$ has $v_i > 0$ but $v_j = 0$, pick
$w \in C$ with $w_j \ne 0$ in an admissible direction; for small $\lambda \in (0,1)$ the mode
$u = (1-\lambda) v + \lambda w$ stays in $C$, keeps every nonzero sign of $v$, and gains a nonzero
$j$-th entry, so $\operatorname{sign}(u) > \operatorname{sign}(v)$. Repeating fills the support. For
Proposition 2, if a maximal $\tau$ had a zero entry, mixing a mode with sign $\tau$ and a full-support
mode would produce a strictly larger sign vector, contradicting maximality. Consistency can be
enforced by flux variability analysis, which removes blocked reactions and fixes the direction of
reversible reactions that can run only one way; after that, flux topes are in bijection with
admissible full sign vectors.

## Sources

- M. P. Gerstl, S. Müller, G. Regensburger, J. Zanghellini, "Flux tope analysis: studying the coordination of reaction directions in metabolic networks", Bioinformatics (2019), <https://doi.org/10.1093/bioinformatics/bty550> (PMC6330010). Section 2.3 (definition of flux topes), Section 2.4, Propositions 1 and 2.
