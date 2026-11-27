# Algorithmic conversion for λΠUN

For [λΠUN](the-type-theory-lambda-pi-u-n.md), six relations are defined simultaneously in three pairs, written $\hat\leftrightarrow$ and $\leftrightarrow$ for neutrals and $\hat\Leftrightarrow$ and $\Leftrightarrow$ for types
and terms. For neutrals, $\hat\leftrightarrow$ synthesizes a type and $\leftrightarrow$ [weak-head reduces](typed-weak-head-reduction-in-lambda-pi-u-n.md) it; for types and terms, $\hat\Leftrightarrow$ weak-head reduces its inputs and
$\Leftrightarrow$ compares weak head normal forms:

- neutral equality, which synthesizes a type: $\Gamma \vdash n\, \hat\leftrightarrow\, m : A$ holds for equal variables $i_x\, \hat\leftrightarrow\, i_x : A$ with $\Gamma \vdash i_x : A$; for applications,
  $n\, t\, \hat\leftrightarrow\, m\, u : G[t]$ when $\Gamma \vdash n \leftrightarrow m : \Pi\, F\, G$ and $\Gamma \vdash t\, \hat\Leftrightarrow\, u : F$; and
  $\mathsf{natrec}\, F\, z\, s\, n\, \hat\leftrightarrow\, \mathsf{natrec}\, G\, z'\, s'\, m : F[n]$ when $\Gamma.\mathsf{N} \vdash F\, \hat\Leftrightarrow\, G$, $\Gamma \vdash z\, \hat\Leftrightarrow\, z' : F[\mathsf{zero}]$,
  $\Gamma \vdash s\, \hat\Leftrightarrow\, s' : \Pi\, \mathsf{N}\, (F \to F[\uparrow, \mathsf{suc}\, i_0])$ and $\Gamma \vdash n \leftrightarrow m : \mathsf{N}$, the type synthesized from the left motive. The second
  relation $\Gamma \vdash n \leftrightarrow m : B$ holds when $\Gamma \vdash n\, \hat\leftrightarrow\, m : A$ and $A$ weak-head reduces to the weak head normal form $B$;
- type equality: $\Gamma \vdash A\, \hat\Leftrightarrow\, B$ when $A$ and $B$ weak-head reduce to weak head normal forms $A'$ and $B'$ with $\Gamma \vdash A' \Leftrightarrow B'$, which holds for
  $\mathsf{U} \Leftrightarrow \mathsf{U}$, $\mathsf{N} \Leftrightarrow \mathsf{N}$, $\Pi\, F\, G \Leftrightarrow \Pi\, H\, E$ when $\Gamma \vdash F\, \hat\Leftrightarrow\, H$ and $\Gamma.F \vdash G\, \hat\Leftrightarrow\, E$, and neutral types $N \Leftrightarrow M$ when
  $\Gamma \vdash N \leftrightarrow M : \mathsf{U}$;
- term equality: $\Gamma \vdash t\, \hat\Leftrightarrow\, u : A$ when the type and both terms weak-head reduce to weak head normal forms $A'$, $t'$, $u'$ with $\Gamma \vdash t' \Leftrightarrow u' : A'$, which
  compares types as terms of $\mathsf{U}$, $\mathsf{zero}$ and $\mathsf{suc}$ structurally at $\mathsf{N}$ (with $\hat\Leftrightarrow$ on the arguments of $\mathsf{suc}$), neutrals at $\mathsf{N}$ or at a
  neutral type by $\Gamma \vdash n \leftrightarrow m : M$ for some $M$, and functions at $\Pi\, F\, G$ by η: $f \Leftrightarrow g$ if $\Gamma.F \vdash f[\uparrow]\, i_0\, \hat\Leftrightarrow\, g[\uparrow]\, i_0 : G$.

The type-directed η-rule makes the checker complete for the extensionality rule of the declarative system.

## Depends on

- [Typed weak head reduction in λΠUN](typed-weak-head-reduction-in-lambda-pi-u-n.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.1 and Figure 6 (algorithm for conversion of neutrals, types and terms).
