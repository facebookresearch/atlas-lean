# Curry–Howard correspondence for second-order propositional logic

The types of System F are exactly the formulas of [second-order propositional logic](second-order-intuitionistic-propositional-logic.md) built from $\to$ and $\forall$. For every context
$\Gamma$ and type $\tau$: $\Gamma \vdash M : \tau$ for some [Church-style System F](../the-five-typing-rules-of-pure-system-f/typing.md) term $M$ if and only if $|\Gamma| \vdash \tau$ in the $\{\forall, \to\}$-fragment of
second-order intuitionistic propositional logic. Here $|\Gamma|$ is the set of types declared in $\Gamma$, forgetting the variable names. Type abstraction $\Lambda \alpha.\, M$ corresponds to ($\forall$I) and type application $M\, \tau$ to ($\forall$E).

## Depends on

- [Second-order intuitionistic propositional logic](second-order-intuitionistic-propositional-logic.md)
- [Extrinsic typing of pure System F terms](../the-five-typing-rules-of-pure-system-f/typing.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.3, Definitions 12.3.1 and 12.3.2 and Theorem 12.3.5 (Curry–Howard isomorphism).
