# Provably total functions of Peano arithmetic

By Kleene's normal form theorem every partial recursive function $f$ of $k$ arguments can be written $f(\vec n) = \pi_2(\mu y.\, t_f(\vec n, y) = 0)$, where $\pi_2$ is
the second inverse of a primitive recursive pairing function and $t_f$ is a primitive recursive function describing a particular algorithm for $f$.
Extend the language of [Peano arithmetic](../../../Logic/first-order-logic/peano-arithmetic-and-robinson-s-q/patheory.md) conservatively by names and defining equations for primitive recursive functions. A recursive
function $f$ is *provably total* (or *provably recursive*) in PA if, for some such algorithm $t_f$,

$$\mathrm{PA} \vdash \forall \vec x\, \exists y\; t_f(\vec x, y) = 0.$$

The notion concerns algorithms rather than extensional functions: $f$ is provably total when one of its algorithms is. Every provably total
function is total recursive, but not every total recursive function is provably total in PA.

## Depends on

- [Peano arithmetic](../../../Logic/first-order-logic/peano-arithmetic-and-robinson-s-q/patheory.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 11.3, the discussion of Kleene's normal form before Definition 11.3.3, Definition 11.3.3 and the remarks after it.
