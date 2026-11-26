# Precision of gradual types and terms

*Type precision* $T \sqsubseteq T'$, read "$T$ is at least as precise as $T'$", is the least relation with $T \sqsubseteq ?$ for every $T$, $B \sqsubseteq B$, and
$T_1 \to T_2 \sqsubseteq T_3 \to T_4$ whenever $T_1 \sqsubseteq T_3$ and $T_2 \sqsubseteq T_4$. It is covariant in both argument and result, and coincides with naive subtyping.

*Term precision* $e \sqsubseteq e'$ on the [GTLC](the-gradually-typed-lambda-calculus.md) is its congruent extension to terms: $k \sqsubseteq k$, $x \sqsubseteq x$,
$\lambda x{:}T_1.\, e_1 \sqsubseteq \lambda x{:}T_2.\, e_2$ if $T_1 \sqsubseteq T_2$ and $e_1 \sqsubseteq e_2$, and $(e_1\, e_1')^\ell \sqsubseteq (e_2\, e_2')^\ell$ if $e_1 \sqsubseteq e_2$ and $e_1' \sqsubseteq e_2'$.
So $e \sqsubseteq e'$ when $e'$ is obtained from $e$ by replacing some type annotations by less precise ones. Precision on values of the cast calculus is
defined in the same way.

## Depends on

- [The gradually typed λ-calculus](the-gradually-typed-lambda-calculus.md)

## Sources

- J. G. Siek, M. M. Vitousek, M. Cimini and J. T. Boyland, "Refined criteria for gradual typing", *1st Summit on Advances in Programming Languages (SNAPL 2015)*, LIPIcs 32, pp. 274–293, 2015, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol032-snapl2015/LIPIcs.SNAPL.2015.274/LIPIcs.SNAPL.2015.274.pdf>: Section 4.3 and Figure 6 (type precision and term precision), and Section 6 (precision for the cast calculus).
