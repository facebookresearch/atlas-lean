# The Cassels–Tate pairing of an abelian variety

Let $K$ be a number field, $\bar K$ an algebraic closure, $A$ an
[abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $K$ and $A^\vee$ its
[dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md). Let $\text{Ш}(K, A)$ and
$\text{Ш}(K, A^\vee)$ be the Shafarevich–Tate groups, the classes in $H^1(G_K, A(\bar K))$ and
$H^1(G_K, A^\vee(\bar K))$ that vanish in $H^1(G_v, A(\bar K_v))$ and $H^1(G_v, A^\vee(\bar K_v))$ at every place
$v$, as in [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](selmer-groups-of-abelian-varieties.md).
Cochains are continuous inhomogeneous cochains, the group law of $\bar K^\times$ is written additively, and for a
global cochain $\alpha$ its restriction to $G_v$ is written $\alpha_v$.

The **Cassels–Tate pairing** is the biadditive map

$$\langle\,,\rangle \colon \text{Ш}(K, A) \times \text{Ш}(K, A^\vee) \to \mathbb{Q}/\mathbb{Z}$$

defined as follows (the Weil pairing definition). Let $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$, and
choose $m \ge 1$ killing both. Let $e_m \colon A[m] \times A^\vee[m] \to \mu_m \subseteq \bar K^\times$ be the pairing
given by the canonical identification of $A^\vee[m]$ with the Cartier dual of $A[m]$, normalized as in Poonen–Stoll,
§12.2, and let $\vee$ be the cup product of cochains it induces.

1. Choose cocycles $\tau \in Z^1(G_K, A[m])$ and $\tau' \in Z^1(G_K, A^\vee[m])$ whose classes map to $a$ and $a'$ under
   the maps induced by $A[m] \subseteq A(\bar K)$ and $A^\vee[m] \subseteq A^\vee(\bar K)$, which are onto
   $H^1(G_K, -)[m]$ by the Kummer sequences.
2. Choose a cochain $\sigma \in C^1(G_K, A[m^2])$ with $m\sigma = \tau$. Then $d\sigma$ takes values in $A[m]$, and
   $d\sigma \vee \tau'$ is a $3$-cocycle with values in $\bar K^\times$. As $H^3(G_K, \bar K^\times) = 0$, there is
   $\bar\varepsilon \in C^2(G_K, \bar K^\times)$ with $d\sigma \vee \tau' = d\bar\varepsilon$.
3. For each place $v$, since the image of $a$ in $H^1(G_v, A(\bar K_v))$ is zero, choose
   $\beta_v \in A(\bar K_v)$ with $d\beta_v$ equal to the image of $\tau_v$, choose $Q_v \in A(\bar K_v)$ with
   $mQ_v = \beta_v$, and let $\rho_v = dQ_v \in Z^1(G_v, A[m^2])$. Then $\sigma_v - \rho_v$ takes values in $A[m]$, and

    $$\bar\gamma_v = (\sigma_v - \rho_v) \vee \tau'_v - \bar\varepsilon_v \in C^2(G_v, \bar K_v^\times)$$

    is a $2$-cocycle, whose class is an element $\bar c_v$ of $\mathrm{Br}(K_v) = H^2(G_v, \bar K_v^\times)$.
4. $\langle a, a' \rangle = \sum_v \mathrm{inv}_v(\bar c_v)$, where $\mathrm{inv}_v \colon \mathrm{Br}(K_v) \to \mathbb{Q}/\mathbb{Z}$ is the
   local invariant map; all but finitely many terms vanish.

The value does not depend on the choices made, nor on $m$ (replacing $m$ by a multiple gives the same value), and
it is biadditive.

## Depends on

- [Abelian scheme](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee$ and the Cartier duality of $A[m]$ and $A^\vee[m]$ (its item 3) that defines $e_m$
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](selmer-groups-of-abelian-varieties.md), for $\text{Ш}(K, A)$ and the local groups
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for the cochain $\bar\varepsilon$ in step 2
- [Local class field theory: cohomology and the existence theorem](../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)
- [Cohomology of profinite groups](../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for continuous cochains and their cup products

## Proof depends on

- [The local invariants of a global class in H² sum to zero](../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/sum-of-local-invariants.md), for the independence of the choice of $\bar\varepsilon$, which is determined up to a global $2$-cocycle
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](selmer-groups-of-abelian-varieties.md), for its item 4: at the places of good reduction prime to $m$ outside a finite set the local choices can be made unramified, so that almost all $\bar c_v$ vanish
- [Tate local duality for abelian varieties](../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-local-duality-for-abelian-varieties.md), for the independence of the local choices of $\beta_v$ and $Q_v$, which uses the local triviality of $a'$ through the compatibility of the local pairings (its items 1 and 3)

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, "The Weil pairing definition", pp. 1143–1144 (the construction above,
  with the normalization of $e_m$ in footnote 21; "One checks that the value is well-defined, and unchanged if $m$ is
  replaced by a prime-to-$p$ multiple"), and §3, pp. 1115–1117, for two other definitions.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Proposition 6.9 and its proof (pp. 78–79, the case $r = 1$, with footnote 14 correcting the order of the
  terms $\beta_{v,1}$ and $\beta_{1,v}$; the special case where $a$ is divisible by $m$ in $H^1(G_K, A)$ is the first
  definition given there).
- M. Flach, "A generalisation of the Cassels-Tate pairing", J. Reine Angew. Math. 412 (1990), 113–127, cited by
  Poonen and Stoll for an outline of the proof that the definition is independent of the choices.
