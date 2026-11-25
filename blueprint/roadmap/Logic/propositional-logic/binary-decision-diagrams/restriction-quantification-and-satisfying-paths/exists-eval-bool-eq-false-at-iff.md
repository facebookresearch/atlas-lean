# Satisfiability with one variable fixed to false

Let $A$ be a proposition over atoms
indexed by natural numbers, let $t$ be its ROBDD, and let $f$ be a natural number. Then $A$
evaluates to true under some valuation $\sigma$ with $\sigma(f) = \mathrm{false}$ if and only
if the cofactor $t[f := \mathrm{false}]$ is not the leaf $\mathrm{false}$.

The variable $f$ can, for instance, play the role of falsum. Without such a constraint, every
proposition over atoms indexed by natural numbers is satisfied by the all-true valuation.
