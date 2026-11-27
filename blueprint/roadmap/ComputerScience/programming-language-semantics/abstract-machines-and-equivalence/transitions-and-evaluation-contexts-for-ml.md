# Transitions and evaluation contexts for ML

For [the ML fragment](an-ml-fragment-with-integer-references.md), let the transition relation $(s, e) \to (s', e')$, between closed expressions with $\mathrm{loc}(e) \subseteq \mathrm{dom}(s)$ and $\mathrm{loc}(e') \subseteq \mathrm{dom}(s')$, be inductively defined by basic reductions, such as
$(s, \mathrm{let}\ x = v\ \mathrm{in}\ e) \to (s, e[v/x])$ for canonical $v$, and by simplification rules that reduce inside the first subexpression still to be evaluated. Then:

1. $s, e \Rightarrow v, s'$ if and only if $(s, e) \to^* (s', v)$;
2. $(s, e) \to (s', e')$ if and only if $e = E[r]$ and $e' = E[r']$ for an evaluation context $E$ and a basic reduction $(s, r) \to (s', r')$, where evaluation contexts are
   $E ::= [-] \mid \mathrm{if}\ E\ \mathrm{then}\ e\ \mathrm{else}\ e \mid E\ op\ e \mid v\ op'\ E \mid op''\ E \mid E\ e \mid v\ E \mid \mathrm{let}\ x = E\ \mathrm{in}\ e$, with $v$ canonical,
   $op \in \{=, +, -, :=, ==, ;, (\,,\,)\}$, $op' \in \{=, +, -, :=, ==, (\,,\,)\}$ (sequencing has no right-hand position, since $v ; e$ reduces at once to $e$) and $op'' \in \{!, \mathrm{ref}, \mathrm{fst}, \mathrm{snd}\}$.

Part 2 rests on unique decomposition: an expression $e$ with $(s, e) \to (s', e')$ is $E[r]$ for exactly one evaluation context $E$ and redex $r$, and every closed
well-typed expression that is not in canonical form has such a decomposition. Well-typedness is needed for existence: $\mathrm{true}\ ()$ is closed and not
canonical, but no basic reduction applies to it.

## Depends on

- [An ML fragment with integer references](an-ml-fragment-with-integer-references.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 4, Lemma 4.1 (Felleisen-style presentation of the transition relation) and the paragraph after it; Appendix A, Section A.5 and Theorem A.2.
