# CTL* model checking is PSPACE-complete

Deciding whether a CTL* state formula is true in a given state of a finite Kripke structure with a total transition relation is PSPACE-complete. For the upper bound, each maximal state subformula $\mathbf{E}\, g$ whose path formula $g$ contains no path quantifier is replaced by a fresh atomic proposition labelling the states where it holds, computed by LTL model checking in polynomial space, and the procedure is repeated, each time reducing the nesting depth of path quantifiers. PSPACE-hardness already holds for formulas of the form $\mathbf{E}\, g$ with $g$ an LTL formula, by the hardness of LTL model checking.

## Depends on

- [State formulas of CTL$^{\ast}$](../ctl/ctl-state-and-path-formulas/state-formula.md)
- [Satisfaction of CTL$^{\ast}$ state formulas](../ctl/ctl-state-and-path-formulas/state-sat.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Model checking CTL* by reduction to LTL](model-checking-ctl-by-reduction-to-ltl.md)
- [Satisfiability, validity and model checking of LTL are PSPACE-complete](../../../TheoryOfComputation/completeness-other-classes/satisfiability-and-model-checking-for-linear-tem/ltl-pspace-complete.md)

## Sources

- E. M. Clarke, E. A. Emerson and A. P. Sistla, "Automatic verification of finite-state concurrent systems using temporal logic specifications", *ACM Transactions on Programming Languages and Systems* 8(2):244–263, 1986, Section 6, Theorem 6.1 and its proof sketch.
