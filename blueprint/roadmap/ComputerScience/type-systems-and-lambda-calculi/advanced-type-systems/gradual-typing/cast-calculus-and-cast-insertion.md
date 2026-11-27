# The cast calculus and cast insertion

The internal cast calculus replaces the implicit consistency checks of the [GTLC](the-gradually-typed-lambda-calculus.md) by explicit casts. With *ground types*
$G ::= B \mid ? \to ?$, its expressions, values and results are

$$f ::= k \mid x \mid \lambda x{:}T.\, f \mid f\, f \mid f : T \Rightarrow^\ell T \mid \mathrm{blame}_T\, \ell, \qquad
v ::= k \mid \lambda x{:}T.\, f \mid v : T_1 \to T_2 \Rightarrow^\ell T_3 \to T_4 \mid v : G \Rightarrow^\ell ?, \qquad r ::= v \mid \mathrm{blame}_T\, \ell.$$

A cast $f : T_1 \Rightarrow^\ell T_2$ has type $T_2$ when $f : T_1$ and $T_1 \sim T_2$, and $\mathrm{blame}_T\, \ell$ has every type $T$.

- **Cast insertion.** $\Gamma \vdash e \rightsquigarrow f : T$ translates a GTLC term; at an application it casts the function to $T_{11} \to T_{12} = \mathrm{fun}(T_1)$ and the argument to
  $T_{11}$, both with the application's label.
- **Reduction.** $(\lambda x{:}T.\, f)\, v \longmapsto [x := v]f$; a function constant applied to a constant reduces by its interpretation, $k\, k' \longmapsto \delta(k, k')$; identity casts at a base type or at $?$ vanish; $v : G \Rightarrow^{\ell_1} ? \Rightarrow^{\ell_2} G \longmapsto v$, while
  $v : G_1 \Rightarrow^{\ell_1} ? \Rightarrow^{\ell_2} G_2 \longmapsto \mathrm{blame}_{G_2}\, \ell_2$ when $G_1 \ne G_2$; a function cast distributes over application,
  $(v_1 : T_1 \to T_2 \Rightarrow^\ell T_3 \to T_4)\, v_2 \longmapsto v_1\, (v_2 : T_3 \Rightarrow^\ell T_1) : T_2 \Rightarrow^\ell T_4$; a cast from $T$ to $?$ or from $?$ to $T$, where
  $T \ne ?$, $T \ne G$ and $T \sim G$ for a ground type $G$, factors through $G$ (rules Ground and Expand); reduction proceeds under evaluation frames, and blame propagates to the top.
- **Evaluation of the GTLC.** $e \Downarrow r$ if $\emptyset \vdash e \rightsquigarrow f : T$ and $f \longmapsto^* r$; $e \Uparrow$ if the reduction of $f$ does not terminate.

The rule for function constants is not in the source's Figure 4, which has constants $k$ but no rule for applying a function constant (Section 4.1 gives $\mathrm{inc}$ as an example of one); without it a well-typed application such as $\mathrm{inc}\; 0$ would be stuck.

## Depends on

- [The gradually typed λ-calculus](the-gradually-typed-lambda-calculus.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 3 and Figure 4 (ground types, the cast calculus, cast insertion and the reduction rules IdBase, IdStar, Succeed, Fail, AppCast, Ground, Expand, Cong and Blame), and the definition of $e \Downarrow r$ in Figure 3.
