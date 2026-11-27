# Binary session types and type safety

Vasconcelos's calculus for binary sessions works as follows.
- **Processes** are $0$, parallel composition, $(\nu xy)P$, conditionals, output $x\, v.P$, input $q\, x(y).P$ (linear or replicated), selection $x \triangleleft l.P$ and branching $x \triangleright \{l_i : P_i\}_{i \in I}$.
- **Channels.** The binder $(\nu xy)P$ creates a channel with two ends, the *co-variables* $x$ and $y$.
- **Reduction.** An output on one end meets an input on its co-variable, and a selection $x \triangleleft l_j$ meets a branching $y \triangleright \{l_i : P_i\}$ with $j \in I$.

**Types** are given by:
- $T ::= \mathrm{bool} \mid \mathrm{end} \mid q\, p$, with qualifiers $q \in \{\mathrm{lin}, \mathrm{un}\}$;
- pretypes $p ::= {?T.U} \mid {!T.U} \mid \&\{l_i : T_i\} \mid \oplus\{l_i : T_i\}$, for receiving, sending, external choice and internal choice;
- recursive types $\mu a.T$, taken up to unfolding.

*Duality* $\overline{T}$ swaps $!$ with $?$ and $\oplus$ with $\&$ and keeps $\overline{\mathrm{end}} = \mathrm{end}$. It is undefined on $\mathrm{bool}$. The typing rules work as follows:
- *context split* $\Gamma_1 \circ \Gamma_2$ divides the linear assumptions between parallel threads, while unrestricted ones are shared;
- the base cases require the remaining context to be unrestricted, so linear channels cannot be discarded;
- input and output *update* the type of the channel end to its continuation;
- the restriction rule types $(\nu xy)P$ by giving $x$ and $y$ dual types $T$ and $\overline{T}$.

A process is *well formed* if each structurally congruent form $(\nu x_1 y_1) \cdots (\nu x_n y_n)(P \mid Q \mid R)$ satisfies three conditions:
- a conditional tests $\mathrm{true}$ or $\mathrm{false}$;
- two threads prefixed at the same variable use it in the same way (input, output, selection or branching);
- threads prefixed at co-variables $x_1$ and $y_1$ form a redex, that is, matching send and receive or a selected label that is offered.

**Theorem.**
1. **Preservation (subject reduction).** If $\Gamma \vdash P$ and $P \to Q$, then $\Gamma \vdash Q$.
2. **Safety.** If $\vdash P$, then $P$ is well formed.
3. **Main result.** If $\vdash P$ and $P \to^\ast Q$, then $Q$ is well formed. Closed typable processes never reach a communication error: no mismatched send and receive, no unoffered label, and no conditional on a channel.

**Proof outline.** Preservation is proved by induction on the reduction, using these properties: context split; unrestricted weakening; strengthening; preservation under structural congruence; inversion; and a substitution lemma for linear and unrestricted values. In the communication case, duality of the types of $x$ and $y$ makes the continuations dual again. Safety holds because dual types make co-variables be used complementarily. The main result follows by induction on the number of reduction steps.

## Background

- [Subject reduction for endpoint typing](subject-reduction-for-endpoint-typing/README.md)
- [Finite binary sessions](finite-binary-sessions/README.md)

## Sources

- V. T. Vasconcelos, "Fundamentals of session types", *Information and Computation* 217:52–70, 2012, <https://www.di.fc.ul.pt/~vv/papers/vasconcelos_fundamental-sessions.pdf>:
    - Sections 2–4: syntax and reduction with co-variable binders, types with lin and un qualifiers, duality (Figures 4 and 7), context split and update, the typing rules (Figure 6), recursive types, and choice types with the selection and branching rules;
    - Section 7: well-formed processes, Theorem 7.1 (main result), Theorem 7.2 (preservation), Theorem 7.3 (safety), and Lemmas 7.1–7.4.
