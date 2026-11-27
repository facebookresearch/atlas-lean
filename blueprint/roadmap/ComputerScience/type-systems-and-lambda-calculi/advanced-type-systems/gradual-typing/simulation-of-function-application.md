# Simulation of function application

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $\vdash \lambda x{:}T_1.\, f : T_1 \to T_2$, $\vdash v : T_1$, $\vdash v_1' : T_1' \to T_2'$, $\vdash v_2' : T_1'$ and
$T_1 \to T_2 \sqsubseteq T_1' \to T_2'$. If $\lambda x{:}T_1.\, f \sqsubseteq v_1'$ and $v \sqsubseteq v_2'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md), then $v_1'\, v_2' \longmapsto^* f'$ for some
$f'$ with $[x := v]f \sqsubseteq f'$ and $\vdash f' : T_2'$. The proof is by induction on the derivation of $\lambda x{:}T_1.\, f \sqsubseteq v_1'$, since $v_1'$ may be a function wrapped in a
series of casts.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Proof depends on

- [Extra cast on the right](extra-cast-on-the-right.md): in the case of an extra wrapper on the right, the argument cast back to the inner domain reduces to a value still related to the left argument

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 10 (simulation of function application).
