# The type theory λΠUN

Expressions of *λΠUN*, in de Bruijn style, are $t, u, A, B ::= i_x \mid \lambda t \mid t\, u \mid \Pi\, A\, B \mid \mathsf{U} \mid \mathsf{N} \mid \mathsf{zero} \mid \mathsf{suc}\, t \mid \mathsf{natrec}\, A\, t\, u\, v$, where $\lambda$, the second argument
of $\Pi$ and the first argument of $\mathsf{natrec}$ bind one index; contexts are lists $\epsilon, \Gamma.A$, and substitutions act by the usual rewrite rules, with $t[u]$ for the
substitution of $u$ for index $0$ and $A \to B = \Pi\, A\, B[\uparrow]$. *Weak head normal forms* are $\lambda t$, $\mathsf{U}$, $\mathsf{N}$, $\Pi\, A\, B$, $\mathsf{zero}$, $\mathsf{suc}\, t$ and neutral
expressions $n ::= i_x \mid n\, t \mid \mathsf{natrec}\, A\, t\, u\, n$.

The judgements $\vdash \Gamma$, $\Gamma \vdash A$, $\Gamma \vdash A = B$, $\Gamma \vdash t : A$ and $\Gamma \vdash t = u : A$ are defined simultaneously by: formation rules for $\mathsf{U}$, $\mathsf{N}$ and $\Pi$;
$\mathsf{N} : \mathsf{U}$ and $\Pi\, F\, G : \mathsf{U}$ for $F : \mathsf{U}$ and $G : \mathsf{U}$ in the extended context; a term of type $\mathsf{U}$ is a type (universe à la Russell); variables,
abstraction, application with $g\, a : G[a]$, $\mathsf{zero}$, $\mathsf{suc}$ and $\mathsf{natrec}\, G\, z\, s\, t : G[t]$ for $z : G[\mathsf{zero}]$ and $s : \Pi\, \mathsf{N}\, (G \to G[\uparrow, \mathsf{suc}\, i_0])$;
conversion of terms and of term equalities along type equality; reflexivity, symmetry, transitivity and congruence rules for every former; and the
computation rules $(\lambda t)\, a = t[a]$, $\mathsf{natrec}\, F\, z\, s\, \mathsf{zero} = z$, $\mathsf{natrec}\, F\, z\, s\, (\mathsf{suc}\, t) = (s\, t)\, (\mathsf{natrec}\, F\, z\, s\, t)$, and the
extensionality rule $f = g : \Pi\, F\, G$ when $f[\uparrow]\, i_0 = g[\uparrow]\, i_0 : G$. With $\mathsf{natrec}$ into $\mathsf{U}$, types can depend on numbers (large elimination). Every judgement
$\Gamma \vdash J$ implies $\vdash \Gamma$, and judgements are stable under well-formed weakenings.

## Depends on

- [Pure type systems and the calculus of constructions](../pure-type-systems-and-the-calculus-of.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 2.1 (Figures 1 and 2, syntax and substitution), Section 2.2 (Figure 3, inference rules), Lemma 2.1 (well-formed context) and Lemma 2.7 (weakening).
