# Simulation of unwrapping

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $\vdash v_1 : T_1 \to T_2$, $\vdash v_2 : T_1$, $\vdash v_1' : T_1' \to T_2'$, $\vdash v_2' : T_1'$ and $T_1 \to T_2 \sqsubseteq T_1' \to T_2'$.
If $(v_1 : T_1 \to T_2 \Rightarrow^\ell T_3 \to T_4) \sqsubseteq v_1'$ and $v_2 \sqsubseteq v_2'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md), then $v_1'\, v_2' \longmapsto^* f'$ for some $f'$
with $(v_1\, (v_2 : T_3 \Rightarrow^\ell T_1)) : T_2 \Rightarrow^\ell T_4 \sqsubseteq f'$: the less precise program simulates the step that unwraps a function cast. The proof is by induction on
the derivation of the first precision hypothesis.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 11 (simulation of unwrapping).
