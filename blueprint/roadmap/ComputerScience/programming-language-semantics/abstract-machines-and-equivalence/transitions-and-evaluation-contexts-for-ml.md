# Transitions and evaluation contexts for ML

For [the ML fragment](an-ml-fragment-with-integer-references.md), let the transition relation $(s, e) \to (s', e')$, between closed expressions with $\mathrm{loc}(e) \subseteq \mathrm{dom}(s)$ and $\mathrm{loc}(e') \subseteq \mathrm{dom}(s')$, be inductively defined by basic reductions, such as
$(s, \mathrm{let}\ x = v\ \mathrm{in}\ e) \to (s, e[v/x])$, $(s, \mathrm{fst}\, (v_1, v_2)) \to (s, v_1)$ and $(s, \mathrm{snd}\, (v_1, v_2)) \to (s, v_2)$ for canonical $v, v_1, v_2$, and by simplification rules that reduce inside the first subexpression still to be evaluated, such as $(s, op''\, e) \to (s', op''\, e')$ if $(s, e) \to (s', e')$, for
$op'' \in \{!, \mathrm{ref}, \mathrm{fst}, \mathrm{snd}\}$: the operand that steps in the premise is the operand of the conclusion. Then:

1. $s, e \Rightarrow v, s'$ if and only if $(s, e) \to^* (s', v)$;
2. $(s, e) \to (s', e')$ if and only if $e = E[r]$ and $e' = E[r']$ for an evaluation context $E$ and a basic reduction $(s, r) \to (s', r')$, where evaluation contexts are
   $E ::= [-] \mid \mathrm{if}\ E\ \mathrm{then}\ e\ \mathrm{else}\ e \mid E\ op\ e \mid v\ op'\ E \mid op''\ E \mid E\ e \mid v\ E \mid \mathrm{let}\ x = E\ \mathrm{in}\ e$, with $v$ canonical,
   $op \in \{=, +, -, :=, ==, ;, (\,,\,)\}$, $op' \in \{=, +, -, :=, ==, (\,,\,)\}$ (sequencing has no right-hand position, since $v ; e$ reduces at once to $e$) and $op'' \in \{!, \mathrm{ref}, \mathrm{fst}, \mathrm{snd}\}$.

The source's table of basic reductions (A.5) prints the $\mathrm{snd}$ rule with result $v_1$; its evaluation rule (A.3) and machine frame (A.6) give $v_2$, and
with $v_1$ part 1 would fail already for $\mathrm{snd}\, (0, 1)$ in the empty state. The same table's unary simplification rule steps $e_1$ in its premise and $e$ in
its conclusion, a misprint of the subscripts.

Part 2 rests on unique decomposition: an expression $e$ with $(s, e) \to (s', e')$ is $E[r]$ for exactly one evaluation context $E$ and redex $r$, and every closed
well-typed expression that is not in canonical form has such a decomposition. Well-typedness is needed for existence: $\mathrm{true}\ ()$ is closed and not
canonical, but no basic reduction applies to it.

## Depends on

- [An ML fragment with integer references](an-ml-fragment-with-integer-references.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 4, Lemma 4.1 (Felleisen-style presentation of the transition relation) and the paragraph after it; Appendix A, Section A.5 and Theorem A.2.
