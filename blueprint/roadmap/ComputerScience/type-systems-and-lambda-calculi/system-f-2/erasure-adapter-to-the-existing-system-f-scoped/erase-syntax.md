# Erasure of Fω terms to System F syntax

The erasure $|t| \in \mathrm{Tm}_{0,m}$ of an [Fω term](../scoped-pure-f-terms/tm.md) $t \in
\mathrm{Tm}_{\Delta,m}$ is the [System F term](../../system-f/scoped-pure-system-f/tm.md) with no
type variables and the same $m$ term variables defined by $|x_i| = x_i$, $|\lambda A.\,b| =
\lambda(\forall \alpha_0).\,|b|$, $|f\,a| = |f|\,|a|$, $|\Lambda_\kappa b| = |b|$ and $|f\,[A]| =
|f|$. It keeps term variables, abstractions and applications, removes type abstractions and type
applications, and replaces every abstraction annotation by the fixed closed type $\forall \alpha_0$.
It is not a type-preserving embedding.
