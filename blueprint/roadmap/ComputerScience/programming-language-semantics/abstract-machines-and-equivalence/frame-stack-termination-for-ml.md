# Frame-stack termination for ML

Decompose evaluation contexts of [the ML fragment](an-ml-fragment-with-integer-references.md) into *frame stacks* $Fs ::= \mathrm{Id} \mid Fs \circ F$ of evaluation frames
$F ::= \mathrm{if}\ [-]\ \mathrm{then}\ e\ \mathrm{else}\ e \mid [-]\ op\ e \mid v\ op'\ [-] \mid op''\ [-] \mid [-]\ e \mid v\ [-] \mid \mathrm{let}\ x = [-]\ \mathrm{in}\ e$, with $v$ canonical,
$op \in \{=, +, -, :=, ==, ;, (\,,\,)\}$, $op' \in \{=, +, -, :=, ==, (\,,\,)\}$ (sequencing has no right-hand position, since $v ; e$ reduces at once to $e$) and $op'' \in \{!, \mathrm{ref}, \mathrm{fst}, \mathrm{snd}\}$, and run the abstract machine on
configurations $\langle s, Fs, e \rangle$ of a state, a closed frame stack and a closed expression with the locations of $Fs$ and $e$ in $\mathrm{dom}(s)$, with steps defined by cases on $e$ and $Fs$, for example
$\langle s, Fs, \mathrm{let}\ x = e_1\ \mathrm{in}\ e_2 \rangle \to \langle s, Fs \circ (\mathrm{let}\ x = [-]\ \mathrm{in}\ e_2), e_1 \rangle$ and
$\langle s, Fs \circ (\mathrm{let}\ x = [-]\ \mathrm{in}\ e), v \rangle \to \langle s, Fs, e[v/x] \rangle$; dereference reads a binding of the state:
$\langle s, Fs \circ (!\, [-]), \ell \rangle \to \langle s, Fs, n \rangle$ if $\ell \in \mathrm{dom}(s)$ and $s(\ell) = n$. Write $\langle s, Fs, e \rangle{\downarrow}$ if the machine reaches some $\langle s', \mathrm{Id}, v \rangle$. Then:

1. for closed $e$ with $\mathrm{loc}(e) \subseteq \mathrm{dom}(s)$, $s, e \Downarrow$ if and only if $\langle s, \mathrm{Id}, e \rangle{\downarrow}$;
2. for such a configuration, $\langle s, Fs, e \rangle{\downarrow}$ if and only if $s, e \Rightarrow v, s'$ and $\langle s', Fs, v \rangle{\downarrow}$ for some $v$ and $s'$;
3. the relation $\langle s, Fs, e \rangle{\downarrow}$ has a direct inductive definition following the structure of $e$ and $Fs$, which allows termination properties to be proved by
   structural induction: one rule for each machine transition, with conclusion the source configuration and premise the target, and the axiom
   $\langle s, \mathrm{Id}, v \rangle{\downarrow}$ for canonical $v$. In particular it has the rule for dereference with premises $\ell \in \mathrm{dom}(s)$, $s(\ell) = n$ and
   $\langle s, Fs, n \rangle{\downarrow}$; the rules that start a binary operation, $\langle s, Fs, e_1\ op\ e_2 \rangle{\downarrow}$ if $\langle s, Fs \circ ([-]\ op\ e_2), e_1 \rangle{\downarrow}$, for
   every $op \in \{=, +, -, :=, ==, ;, (\,,\,)\}$, sequencing included; the rule that starts a $\mathrm{let}$: $\langle s, Fs, \mathrm{let}\ x = e_1\ \mathrm{in}\ e_2 \rangle{\downarrow}$ if
   $\langle s, Fs \circ (\mathrm{let}\ x = [-]\ \mathrm{in}\ e_2), e_1 \rangle{\downarrow}$; and the rule that combines two values, for $op \in \{=, +, -, ==, (\,,\,)\}$ only, since
   assignment has its own rule, which changes the state.

The source's tables (A.6 and A.7) print the dereference premise as $(\ell \mapsto n) \in \mathrm{dom}(s)$, a binding rather than a member of the domain, A.7 omits the
rule that starts a $\mathrm{let}$ and the one that starts a sequence, and its combining rule wrongly lists $:=$. Without the missing rules, the termination of
$\mathrm{let}\ x = 0\ \mathrm{in}\ x$ and of $()\, ;\, ()$ in the empty state, which the machine reaches in two steps each, is not derivable.

## Depends on

- [An ML fragment with integer references](an-ml-fragment-with-integer-references.md)

## Proof depends on

- [Transitions and evaluation contexts for ML](transitions-and-evaluation-contexts-for-ml.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 4 (Figure 4, frame stacks, and the key observation after it); Appendix A, Sections A.6–A.7 and Theorems A.3 and A.4.
