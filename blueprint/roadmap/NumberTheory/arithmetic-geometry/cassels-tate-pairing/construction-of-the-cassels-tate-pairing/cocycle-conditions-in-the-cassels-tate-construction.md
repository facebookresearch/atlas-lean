# The cochains of the Cassels–Tate construction are cocycles

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md)
over $K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $m \ge 1$, and
$a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$ killed by $m$. Let $\vee$ be the cup product of cochains through the
[Weil pairing](weil-pairing-through-a-poincare-divisor.md) $e_m \colon A[m] \times A^\vee[m] \to \bar K^\times$, the group law of
$\bar K^\times$ written additively. **Cassels–Tate data** for $(a, a', m)$, as in the construction of
[the Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md), are: cocycles $\tau \in Z^1(G_K, A[m])$ and
$\tau' \in Z^1(G_K, A^\vee[m])$ whose classes map to $a$ and $a'$; a cochain $\sigma \in C^1(G_K, A[m^2])$ with $m\sigma = \tau$;
a cochain $\bar\varepsilon \in C^2(G_K, \bar K^\times)$ with $d\bar\varepsilon = d\sigma \vee \tau'$; and, for each place $v$, points
$\beta_v, Q_v \in A(\bar K_v)$ with $d\beta_v$ the image of $\tau_v$ and $mQ_v = \beta_v$, and $\rho_v = dQ_v$. They exist, by the
Kummer sequences, the vanishing of $H^3(G_K, \bar K^\times)$ and the local triviality of $a$, once 1 below holds. Then:

1. $d\sigma \in C^2(G_K, A[m^2])$ takes values in $A[m]$, and $d\sigma \vee \tau' \in C^3(G_K, \bar K^\times)$ is a cocycle.
2. For every place $v$, $\rho_v$ is a cocycle with values in $A[m^2]$ and $m\rho_v = \tau_v$; $\sigma_v - \rho_v$ takes values
   in $A[m]$, and

    $$\bar\gamma_v = (\sigma_v - \rho_v) \vee \tau'_v - \bar\varepsilon_v \in C^2(G_v, \bar K_v^\times)$$

    is a cocycle.

Proof. For cochains $x \in C^p(G, A[m])$ and $y \in C^q(G, A^\vee[m])$, $d(x \vee y) = dx \vee y + (-1)^p x \vee dy$, as $e_m$
is biadditive and Galois-equivariant. In 1, $m\,d\sigma = d(m\sigma) = d\tau = 0$, and
$d(d\sigma \vee \tau') = d(d\sigma) \vee \tau' + d\sigma \vee d\tau' = 0$. In 2, $m\,dQ_v = d\beta_v = \tau_v$, so
$m^2 \rho_v = m\tau_v = 0$, and $\rho_v = dQ_v$ is a cocycle; then $m(\sigma_v - \rho_v) = \tau_v - \tau_v = 0$, and, as
$d(\sigma_v - \rho_v) = d\sigma_v$ and $d\tau'_v = 0$,
$d\bar\gamma_v = d\sigma_v \vee \tau'_v - (d\sigma \vee \tau')_v = 0$.

## Depends on

- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for $\text{Ш}(K, A)$, the local groups and the Kummer sequences
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for the existence of $\bar\varepsilon$
- [The Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for continuous cochains and their cup products (its item 3)

## Proof depends on

- [The Weil pairing is biadditive, Galois-equivariant and compatible in m](bilinearity-of-the-weil-pairing.md), for the cup product $\vee$ and its coboundary formula (its items 1 and 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for $d(x \cup y) = dx \cup y + (-1)^p x \cup dy$ (its item 3)

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, pp. 1143–1144 ("Then $d\sigma$ takes values in $A[m]$, and $d\sigma \vee \tau'$
  represents an element of $H^3(k^{\mathrm{sep}*}) = 0$"; "Note that $\sigma_v - \rho_v$ takes values in $A[m]$. Then
  $\bar\gamma_v$ … is a 2-cocycle"); §3.2, p. 1117, for the formula $d(x \cup y) = dx \cup y + (-1)^{\deg x} x \cup dy$, for
  which they cite Atiyah and Wall, p. 106 (not read).
