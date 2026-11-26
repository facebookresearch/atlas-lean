# Extra cast on the right

In the [cast calculus](cast-calculus-and-cast-insertion.md), suppose $\vdash v : T$, $\vdash v' : T_1'$, $T \sqsubseteq T_1'$ and $T \sqsubseteq T_2'$, for values $v$ and $v'$ with $v \sqsubseteq v'$ in
[cast-calculus precision](precision-of-gradual-types-and-terms.md). Then $(v' : T_1' \Rightarrow^\ell T_2') \longmapsto^* v''$ for some value $v''$ with $v \sqsubseteq v''$: a cast between two types less
precise than the type of $v$ cannot fail on a value related to $v$. The proof is by case analysis on $T_1'$ and $T_2'$.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 8 (extra cast on the right).
