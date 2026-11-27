# The Curry–Howard correspondence for the conjunction–implication fragment

Read simple types built from atomic types by $\wedge$ (product) and $\Rightarrow$ (function) as propositions of intuitionistic logic. Consider natural deductions in which the hypotheses are grouped into *parcels* labelled by integers, so that discharging an implication discharges one parcel. Translate as follows:

1. a hypothesis $A$ in parcel $i$ corresponds to the variable $x^A_i$;
2. $\wedge$-introduction from deductions of $A$ and $B$ corresponds to the pair $\langle u, v\rangle$;
3. the two $\wedge$-eliminations correspond to the projections $\pi_1 t$ and $\pi_2 t$;
4. $\Rightarrow$-introduction discharging parcel $i$ in a deduction of $B$ corresponds to the abstraction $\lambda x^A_i.\, v$;
5. $\Rightarrow$-elimination from deductions of $A$ and $A \Rightarrow B$ corresponds to the application $t\,u$.

This is a bijection between deductions of $A$ from labelled parcels of hypotheses and typed terms of type $A$, whose free variables are the hypotheses. It is an isomorphism: under it, the conversions of natural deduction correspond exactly to $\beta$-conversion and the projection conversions of the typed calculus. These are the conversions that remove an introduction immediately followed by an elimination. In particular normal deductions correspond to normal terms, and the normal form theorem for typed terms is the normalization theorem for natural deduction.

The labelled parcels matter. If hypotheses of the same formula are not distinguished, $\lambda x^A.\, \lambda y^A.\, x$ and $\lambda x^A.\, \lambda y^A.\, y$ erase to the same deduction of $A \Rightarrow A \Rightarrow A$, and only the correspondence between provability and inhabitation remains.

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, <https://www.paultaylor.eu/stable/prot.pdf>, Chapter 3: Section 3.5 (description of the isomorphism) and Section 3.6 (relevance of the isomorphism: conversions, normality and reduction correspond).
- W. A. Howard, "The formulae-as-types notion of construction", in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980.
