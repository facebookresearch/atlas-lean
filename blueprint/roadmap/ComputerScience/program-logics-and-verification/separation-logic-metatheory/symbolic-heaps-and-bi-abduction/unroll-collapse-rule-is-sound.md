# The unroll-collapse rule is sound

For [symbolic heaps with list segments](symbolic-heaps-with-list-segments.md), if $x$ is a variable not free in $\Pi, E_1, E_2, \Sigma, \Pi', \Sigma'$, and both entailments

$$\Pi \wedge E_1 = E_2 \mid \Sigma \vdash \Pi' \mid \Sigma' \qquad\text{and}\qquad \Pi \wedge E_1 \ne E_2 \wedge x \ne E_2 \mid E_1 \mapsto x \ast x \mapsto E_2 \ast \Sigma \vdash \Pi' \mid \Sigma'$$

are valid, then $\Pi \mid \mathrm{ls}(E_1, E_2) \ast \Sigma \vdash \Pi' \mid \Sigma'$ is valid. So for entailment it suffices to check list segments of lengths zero and two; length one need not be checked, since a consequent that accepts a segment of length two also accepts one of length one.

## Depends on

- [Symbolic heaps with list segments](symbolic-heaps-with-list-segments.md)

## Sources

- J. Berdine, C. Calcagno and P. W. O'Hearn, "A decidable fragment of separation logic", *FSTTCS 2004*, LNCS 3328, Springer, 2004, pp. 97–109; extended version <https://jberdine.github.io/pub/2004_fsttcs.pdf>, Section 3, Proposition 2.
