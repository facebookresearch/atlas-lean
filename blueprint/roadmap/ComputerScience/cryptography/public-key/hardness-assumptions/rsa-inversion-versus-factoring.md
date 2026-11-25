# RSA inversion versus factoring

Determine whether an efficient RSA inverter necessarily gives an efficient factoring algorithm. Factoring already gives RSA inversion; the reverse direction is the issue.

## What would settle it

Fix the RSA modulus/exponent distribution and success convention. Construct a classical probabilistic polynomial-time oracle reduction from non-negligible inversion on random units to factoring, with a proved success bound. A generic-ring result does not settle arbitrary algorithms; quantum factoring is already possible by a different route.

## Status

The cited sources, in the versions cited, record the partial results below; they do not pose the question in this form, and this page does not certify its present status. This status evidence is older or incomplete; check later literature before relying on it.

Boneh and Venkatesan show that an algebraic reduction from factoring to breaking low-exponent RSA would yield an efficient factoring algorithm. Aggarwal and Maurer prove that a generic ring algorithm breaking RSA can be converted into a factoring algorithm. Neither settles the question for arbitrary algorithms.

This page records the research target above and asserts no theorem or present-status certification.

## Sources

- D. Boneh and R. Venkatesan, *Breaking RSA may not be equivalent to factoring*, EUROCRYPT 1998, abstract. <http://crypto.stanford.edu/~dabo/abstracts/no_rsa_red.html>
- D. Aggarwal and U. Maurer, *Breaking RSA generically is equivalent to factoring*, IACR ePrint 2008/260 (EUROCRYPT 2009), abstract. <https://eprint.iacr.org/2008/260>
