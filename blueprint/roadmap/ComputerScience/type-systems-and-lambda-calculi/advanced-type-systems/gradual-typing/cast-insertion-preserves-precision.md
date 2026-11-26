# Cast insertion preserves precision

If $\Gamma \vdash e \rightsquigarrow f : T$ and $\Gamma' \vdash e' \rightsquigarrow f' : T'$ by [cast insertion](cast-calculus-and-cast-insertion.md), $\Gamma \sqsubseteq \Gamma'$ pointwise and $e \sqsubseteq e'$ in
[term precision](precision-of-gradual-types-and-terms.md), then $\Gamma, \Gamma' \vdash f \sqsubseteq f'$ in [cast-calculus precision](precision-of-gradual-types-and-terms.md) and $T \sqsubseteq T'$.

The lemma fails for the original formulation of the GTLC, whose cast insertion had a separate rule for applying a term of type $?$, casting it to $T \to ?$:
$e_1 = ((\lambda g{:}? \to ?.\, g)\, (\lambda x{:}?.\, x))\, 42 \sqsubseteq e_2 = ((\lambda g{:}?.\, g)\, (\lambda x{:}?.\, x))\, 42$, but their translations are not related.

## Depends on

- [Precision of gradual types and terms](precision-of-gradual-types-and-terms.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, 274–293, <https://doi.org/10.4230/LIPIcs.SNAPL.2015.274>: Section 6, Lemma 6 (cast insertion preserves precision) and the counterexample after it.
