# The gradually typed λ-calculus

The gradually typed λ-calculus (GTLC) extends the simply typed λ-calculus with an *unknown type* $?$. Its types and expressions are

$$T ::= B \mid T \to T \mid ?, \qquad B ::= \mathrm{int} \mid \mathrm{bool}, \qquad e ::= k \mid x \mid \lambda x{:}T.\, e \mid (e\, e)^\ell,$$

with constants $k$, each of a base type or of a type $B_1 \to B_2$ between base types (such as $\mathrm{inc} : \mathrm{int} \to \mathrm{int}$), every function constant $k : B_1 \to B_2$ coming with a total interpretation $\delta(k, \cdot)$ from the constants of type $B_1$ to those of type $B_2$ (for example $\delta(\mathrm{inc}, n) = n + 1$), blame labels $\ell$ marking source positions (all distinct), and $\lambda x.\, e$ abbreviating $\lambda x{:}?.\, e$. A type is *static* if
$?$ does not occur in it.

- **Consistency.** $T_1 \sim T_2$ is the least relation with $? \sim T$, $T \sim ?$, $B \sim B$, and $T_1 \to T_2 \sim T_3 \to T_4$ whenever $T_1 \sim T_3$ and $T_2 \sim T_4$. It is
  reflexive and symmetric but not transitive.
- **Function matching.** $\mathrm{fun}(T_1 \to T_2) = T_1 \to T_2$ and $\mathrm{fun}(?) = ? \to ?$.
- **Typing.** Constants, variables and abstractions are typed as in the simply typed λ-calculus; for application, if $\Gamma \vdash e_1 : T_1$, $\Gamma \vdash e_2 : T_2$,
  $\mathrm{fun}(T_1) = T_{11} \to T_{12}$ and $T_2 \sim T_{11}$, then $\Gamma \vdash (e_1\, e_2)^\ell : T_{12}$.

On fully annotated terms, those with no $?$, consistency is equality and the GTLC is the simply typed λ-calculus; with every annotation $?$ it
accepts all terms of the dynamically typed λ-calculus once constants are cast to $?$. The dynamic semantics is given by translation into the
[cast calculus](cast-calculus-and-cast-insertion.md).

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 3 and Figure 3 (syntax, consistency, function matching and typing of the GTLC).
