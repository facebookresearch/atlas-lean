# The Cassels–Tate pairing does not depend on the choices

Let $K$, $A$, $A^\vee$, $m$, $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$ be as in
[The cochains of the Cassels–Tate construction are cocycles](cocycle-conditions-in-the-cassels-tate-construction.md), and for
Cassels–Tate data for $(a, a', m)$ let $\bar c_v \in \mathrm{Br}(K_v)$ be the class of the cocycle $\bar\gamma_v$.

1. For fixed global choices $\tau$, $\tau'$, $\sigma$ and $\bar\varepsilon$, the class $\bar c_v$ does not depend on the local
   choices of $\beta_v$ and $Q_v$. Hence $\bar c_v = 0$ for all but finitely many $v$, whatever the local choices.
2. The sum $\sum_v \mathrm{inv}_v(\bar c_v) \in \mathbb{Q}/\mathbb{Z}$ does not depend on the choices of $\tau$, $\tau'$, $\sigma$ and
   $\bar\varepsilon$.

So, for fixed $m$, the value $\sum_v \mathrm{inv}_v(\bar c_v)$ of the construction of
[the Cassels–Tate pairing](../cassels-tate-pairing-of-an-abelian-variety.md) depends only on $a$ and $a'$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the local choices: replacing $Q_v$ by $Q_v + x$ with $x \in A[m]$ changes $\bar\gamma_v$ by the coboundary
  $-d(x \vee \tau'_v)$; replacing $\beta_v$ by $\beta_v + P$ with $P \in A(K_v)$ changes $\bar c_v$ by minus the cup product
  of the Kummer class of $P$ with the class of $\tau'_v$, which is the Kummer class of a point of $A^\vee(K_v)$ because
  $a'$ is locally trivial, and so vanishes by
  [the comparison of the Weil pairing with Cartier duality](weil-pairing-and-cartier-duality.md) (its item 2); then 1
  follows from the vanishing of $\bar c_v$ outside the finite set $T$ of the places of bad reduction, those above the primes dividing $m$, the archimedean places and
  the places where the global cochains ramify or take non-unit values, for unramified choices, as on the construction page;
- the choice of $\bar\varepsilon$, fixed up to a global $2$-cocycle $z$, which changes the sum by
  $-\sum_v \mathrm{inv}_v(z_v) = 0$;
- the choice of $\sigma$, fixed up to a cochain $s$ with values in $A[m]$: take $\bar\varepsilon + s \vee \tau'$, and
  $\bar\gamma_v$ is unchanged;
- the choice of $\tau$, fixed up to coboundaries $dx$ with $x \in A[m]$ and up to Kummer images $dR$ of points
  $mR \in A(K)$, by the Kummer sequence: change $\sigma$, $\beta_v$ and $Q_v$ compatibly (by $dy$ with $my = x$, by $x$ and by
  $y$; or by $dR'$ with $mR' = R$, by $R$ and by $R'$), and $\bar\gamma_v$ is unchanged;
- the choice of $\tau'$, fixed up to coboundaries $dx'$ with $x' \in A^\vee[m]$, which change $\bar\varepsilon$ by $d\sigma \vee x'$
  and $\bar\gamma_v$ by the coboundary $-d((\sigma_v - \rho_v) \vee x')$, and up to Kummer images of points of $A^\vee(K)$,
  where the reciprocity law and local duality enter; Poonen and Stoll refer to Flach for an outline of the proof that
  the definition is independent of the choices.

## Depends on

- [The cochains of the Cassels–Tate construction are cocycles](cocycle-conditions-in-the-cassels-tate-construction.md), for the Cassels–Tate data and the classes $\bar c_v$
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local invariant maps (its item 2)

## Proof depends on

- [The local invariants of a global class in H² sum to zero](../../../algebraic-number-theory/adeles-class-field-theory/reciprocity-law/sum-of-local-invariants.md), for the choice of $\bar\varepsilon$
- [The Weil pairing and the Cartier duality of A[m] and its dual](weil-pairing-and-cartier-duality.md), for the orthogonality of Kummer images in the local choices (its item 2)
- [The Weil pairing is biadditive, Galois-equivariant and compatible in m](bilinearity-of-the-weil-pairing.md), for the coboundary formula of $\vee$
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](../selmer-groups-of-abelian-varieties.md), for the Kummer sequences, and for the unramified choices outside $T$ (its item 5)

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, p. 1144 ("One checks that the value is well-defined, and unchanged if $m$ is
  replaced by a prime-to-$p$ multiple", and the reference to [Fl], "which also outlines a proof that the definition is
  independent of choices made"); §3.2, p. 1117, for the analogous remark on the Albanese–Picard definition, "In proving
  independence of the choice of $\beta_v$ one uses the local triviality of $a'$, which has not been used so far".
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, proof of Proposition 6.9, p. 79 ("It is not too difficult to check that the pairing is independent of the
  choices made").
- M. Flach, "A generalisation of the Cassels-Tate pairing", J. Reine Angew. Math. 412 (1990), 113–127, as cited by
  Poonen and Stoll, §12.2, p. 1144; not read.
