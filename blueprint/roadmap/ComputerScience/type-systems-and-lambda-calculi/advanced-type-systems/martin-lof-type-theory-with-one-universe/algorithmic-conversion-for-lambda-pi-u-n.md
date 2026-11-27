# Algorithmic conversion for λΠUN

For [λΠUN](the-type-theory-lambda-pi-u-n.md), six relations are defined simultaneously in three pairs, written $\hat\leftrightarrow$ and $\leftrightarrow$ for neutrals and $\hat\Leftrightarrow$ and $\Leftrightarrow$ for types
and terms. For neutrals, $\hat\leftrightarrow$ synthesizes a type and $\leftrightarrow$ [weak-head reduces](typed-weak-head-reduction-in-lambda-pi-u-n.md) it; for types and terms, $\hat\Leftrightarrow$ weak-head reduces its inputs and
$\Leftrightarrow$ compares weak head normal forms:

- **neutral equality**, which synthesizes a type: $\Gamma \vdash i_x\, \hat\leftrightarrow\, i_x : A$ if $\Gamma \vdash i_x : A$; $\Gamma \vdash n\, t\, \hat\leftrightarrow\, m\, u : G[t]$ if
  $\Gamma \vdash n \leftrightarrow m : \Pi\, F\, G$ and $\Gamma \vdash t\, \hat\Leftrightarrow\, u : F$; $\Gamma \vdash \mathsf{natrec}\, F\, z\, s\, n\, \hat\leftrightarrow\, \mathsf{natrec}\, G\, z'\, s'\, m : F[n]$ if
  $\Gamma.\mathsf{N} \vdash F\, \hat\Leftrightarrow\, G$, $\Gamma \vdash z\, \hat\Leftrightarrow\, z' : F[\mathsf{zero}]$, $\Gamma \vdash s\, \hat\Leftrightarrow\, s' : \Pi\, \mathsf{N}\, (F \to F[\uparrow, \mathsf{suc}\, i_0])$ and
  $\Gamma \vdash n \leftrightarrow m : \mathsf{N}$, the type being synthesized from the left motive; and $\Gamma \vdash n \leftrightarrow m : B$ if $\Gamma \vdash A \longrightarrow^* B$ with $B$ a weak head
  normal form and $\Gamma \vdash n\, \hat\leftrightarrow\, m : A$;
- **type equality:** $\Gamma \vdash A\, \hat\Leftrightarrow\, B$ if $\Gamma \vdash A \longrightarrow^* A'$ and $\Gamma \vdash B \longrightarrow^* B'$ with weak head normal forms $A'$, $B'$ and $\Gamma \vdash A' \Leftrightarrow B'$;
  then $\Gamma \vdash \mathsf{U} \Leftrightarrow \mathsf{U}$ and $\Gamma \vdash \mathsf{N} \Leftrightarrow \mathsf{N}$ if $\vdash \Gamma$; $\Gamma \vdash \Pi\, F\, G \Leftrightarrow \Pi\, H\, E$ if $\Gamma \vdash F$,
  $\Gamma \vdash F\, \hat\Leftrightarrow\, H$ and $\Gamma.F \vdash G\, \hat\Leftrightarrow\, E$; and $\Gamma \vdash N \Leftrightarrow M$ for neutral types if $\Gamma \vdash N \leftrightarrow M : \mathsf{U}$;
- **term equality:** $\Gamma \vdash t\, \hat\Leftrightarrow\, u : A$ if $\Gamma \vdash A \longrightarrow^* A'$, $\Gamma \vdash t \longrightarrow^* t' : A$ and $\Gamma \vdash u \longrightarrow^* u' : A$ with weak head normal forms
  $A'$, $t'$, $u'$ and $\Gamma \vdash t' \Leftrightarrow u' : A'$; then
  - $\Gamma \vdash A \Leftrightarrow B : \mathsf{U}$ if $\Gamma \vdash A : \mathsf{U}$, $\Gamma \vdash B : \mathsf{U}$ and $\Gamma \vdash A \Leftrightarrow B$;
  - $\Gamma \vdash \mathsf{zero} \Leftrightarrow \mathsf{zero} : \mathsf{N}$ if $\vdash \Gamma$, and $\Gamma \vdash \mathsf{suc}\, t \Leftrightarrow \mathsf{suc}\, u : \mathsf{N}$ if $\Gamma \vdash t\, \hat\Leftrightarrow\, u : \mathsf{N}$;
  - neutrals at $\mathsf{N}$: $\Gamma \vdash n \Leftrightarrow m : \mathsf{N}$ if $\Gamma \vdash n \leftrightarrow m : \mathsf{N}$, the neutral comparison at $\mathsf{N}$ itself;
  - neutrals at a neutral type $N$: $\Gamma \vdash n \Leftrightarrow m : N$ if $\Gamma \vdash n : N$, $\Gamma \vdash m : N$ and $\Gamma \vdash n \leftrightarrow m : M$ for some $M$; only here may the
    synthesized type differ syntactically from the expected one;
  - functions, by η: $\Gamma \vdash f \Leftrightarrow g : \Pi\, F\, G$ if $\Gamma \vdash F$, $\Gamma \vdash f : \Pi\, F\, G$, $\Gamma \vdash g : \Pi\, F\, G$ and
    $\Gamma.F \vdash f[\uparrow]\, i_0\, \hat\Leftrightarrow\, g[\uparrow]\, i_0 : G$.

For example, in the context $X : \mathsf{U}, x : X$ the comparison of $x$ with itself synthesizes $X$, so it relates $x$ to itself at $X$ but not at $\mathsf{N}$.

The type-directed η-rule makes the checker complete for the extensionality rule of the declarative system.

## Depends on

- [Typed weak head reduction in λΠUN](typed-weak-head-reduction-in-lambda-pi-u-n.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.1 and Figure 6 (algorithm for conversion of neutrals, types and terms).
