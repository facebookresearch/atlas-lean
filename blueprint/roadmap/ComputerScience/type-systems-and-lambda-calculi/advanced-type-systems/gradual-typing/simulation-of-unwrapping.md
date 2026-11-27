# Simulation of unwrapping

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $\vdash v_1 : T_1 \to T_2$, $T_1 \to T_2 \sim T_3 \to T_4$ (so that the function cast below is well typed), $\vdash v_2 : T_3$, $\vdash v_1' : T_1' \to T_2'$,
$\vdash v_2' : T_1'$ and $T_3 \to T_4 \sqsubseteq T_1' \to T_2'$.
If $(v_1 : T_1 \to T_2 \Rightarrow^\ell T_3 \to T_4) \sqsubseteq v_1'$ and $v_2 \sqsubseteq v_2'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md), then $v_1'\, v_2' \longmapsto^* f'$ for some $f'$
with $(v_1\, (v_2 : T_3 \Rightarrow^\ell T_1)) : T_2 \Rightarrow^\ell T_4 \sqsubseteq f'$: the less precise program simulates the step that unwraps a function cast. The proof is by induction on
the derivation of the first precision hypothesis. The source's Lemma 11 types $v_2$ at $T_1$ and compares $T_1 \to T_2$ with $T_1' \to T_2'$; with its Figure 4 typing
and rule AppCast, the argument of the applied wrapper has the wrapper's domain $T_3$, and $v_2 : T_3 \Rightarrow^\ell T_1$ is well typed only then. For example, wrap
$\lambda x{:}\mathrm{Int}.\, 0$ from $\mathrm{Int} \to \mathrm{Int}$ to $? \to \mathrm{Int}$ on both sides and take $v_2 = 0$, $v_2' = 0 : \mathrm{Int} \Rightarrow ?$: the printed hypotheses hold, but $0 : ? \Rightarrow \mathrm{Int}$ is not well typed.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Proof depends on

- [Extra cast on the right](extra-cast-on-the-right.md): in the case of an extra wrapper on the right, the argument cast back to the inner domain reduces to a value still related to the left argument

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 11 (simulation of unwrapping), with the argument typed at the wrapper's domain; Figure 4 (typing of casts and rule AppCast).
