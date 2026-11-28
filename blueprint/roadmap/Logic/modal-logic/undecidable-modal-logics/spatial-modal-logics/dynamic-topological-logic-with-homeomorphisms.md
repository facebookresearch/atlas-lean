# Dynamic topological logic with homeomorphisms is undecidable

Satisfiability of dynamic topological formulas, which combine topological interior and closure with next-time, always and eventually along the orbits of a map, is undecidable over dynamic topological systems whose maps are homeomorphisms, even in models with finitely many iterations.

**Dynamic topological structures.** A *dynamic topological structure* is a pair $(\mathfrak{T}, g)$ of a topological space $\mathfrak{T} = (\Delta, \mathbf{I})$, with interior operator $\mathbf{I}$ and closure operator $\mathbf{C}$, and a continuous map $g : \Delta \to \Delta$. Formulas are built from propositional variables by Boolean connectives and the operators $\mathsf{A}$ (interior), $\mathsf{a}$ (closure), $\mathsf{L}$ (next time), $\mathsf{B}$ (always in the future) and $\mathsf{b}$ (eventually).

**Models with $N$ iterations.** For $N \leq \omega$, a model is $\mathfrak{M} = ((\mathfrak{T}, g), \mathfrak{V}, N)$ with a valuation $\mathfrak{V}$ of the variables in $\Delta$. Let $N' = N + 1$ if $N < \omega$ and $N' = \omega$ otherwise. For $m < N'$ the truth relation $(\mathfrak{M}, w) \models_m \varphi$ is: $w \in \mathfrak{V}(p)$ for a variable $p$; Boolean clauses as usual; $(\mathfrak{M}, w) \models_m \mathsf{A}\varphi$ iff $w \in \mathbf{I}\{v : (\mathfrak{M}, v) \models_m \varphi\}$, and similarly for $\mathsf{a}$ with $\mathbf{C}$; $(\mathfrak{M}, w) \models_m \mathsf{L}\varphi$ iff $m + 1 < N'$ and $(\mathfrak{M}, g(w)) \models_{m+1} \varphi$; $(\mathfrak{M}, w) \models_m \mathsf{B}\varphi$ iff $(\mathfrak{M}, g^n(w)) \models_{m+n} \varphi$ for every $n > 0$ with $m + n < N'$; and $(\mathfrak{M}, w) \models_m \mathsf{b}\varphi$ iff this holds for some such $n$. A formula is *satisfiable in models with finite iterations* if $(\mathfrak{M}, w) \models_0 \varphi$ for some model with $N < \omega$ and some $w$.

**Theorem (Konev, Kontchakov, Wolter and Zakharyaschev).** If the maps of dynamic topological structures are required to be homeomorphisms, satisfiability of these formulas is undecidable, even in models with finite iterations.

For continuous maps, satisfiability in models with finite iterations is decidable, but not in primitive recursive time (Gabelaia, Kurucz, Wolter and Zakharyaschev).

## Depends on

- [Topological space](../../../../Topology/topological-spaces/topological-space.md)
- [Homeomorphism](../../../../Topology/topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The copy read cites the undecidability without proof; a good expansion would give the reduction of Konev, Kontchakov, Wolter and Zakharyaschev and link the undecidable problem it starts from.

## Sources

- B. Konev, R. Kontchakov, F. Wolter and M. Zakharyaschev, "On dynamic topological and metric logics", *Studia Logica* 84(1):129–160, 2006, doi:10.1007/s11225-006-9005-x (original source, cited beside the copy read).
- D. Gabelaia, A. Kurucz, F. Wolter and M. Zakharyaschev, "Non-primitive recursive decidability of products of modal logics with expanding domains", *Annals of Pure and Applied Logic* 142(1–3):245–268, 2006, doi:10.1016/j.apal.2006.01.001; read in the authors' open-access copy at <http://titan.dcs.bbk.ac.uk/~michael/expand.pdf>: Section 4 (dynamic topological structures, models with $N$ iterations, the undecidability for homeomorphisms and Theorem 4).
