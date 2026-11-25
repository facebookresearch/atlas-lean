# Structural lemmas for typing judgments

Consider the simply typed λ-calculus with booleans (`true`, `false` and conditionals) and arrow types, with typing judgments $\Gamma \vdash t \in T$ for contexts $\Gamma$ given as partial maps from variables to types, and with $[x := v]\,t$ the result of replacing the free occurrences of $x$ in $t$ by a closed term $v$ (so no variable capture arises). Then:

- *canonical forms*: a closed value of type $\mathrm{Bool}$ is `true` or `false`, and a closed value of type $T_1 \to T_2$ is an abstraction $\lambda x{:}T_1.\, u$;
- *free variables are typed*: if $x$ appears free in $t$ and $\Gamma \vdash t \in T$, then $\Gamma$ assigns a type to $x$;
- *context invariance*: if $\Gamma \vdash t \in T$ and $\Gamma'$ agrees with $\Gamma$ on every variable free in $t$, then $\Gamma' \vdash t \in T$; in particular, adding a binding for a variable not free in $t$ preserves typing;
- *substitution*: if $\Gamma, x{:}U \vdash t \in T$ and $\vdash v \in U$ in the empty context, then $\Gamma \vdash [x := v]\,t \in T$.

## Sources

- B. C. Pierce et al., *Software Foundations*, chapter StlcProp, version 4.0, <https://softwarefoundations.cis.upenn.edu/sf-4.0/StlcProp.html>, lemmas `canonical_forms_bool`, `canonical_forms_fun`, `free_in_context`, `context_invariance` and `substitution_preserves_typing`
