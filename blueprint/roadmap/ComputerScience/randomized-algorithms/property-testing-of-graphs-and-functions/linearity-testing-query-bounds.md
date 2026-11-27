# Linearity testing: amplification and three queries are necessary

Repeating the BLR test $k$ times reads at most $3k$ values, accepts every linear function (parity) $\chi_S$ with probability $1$, and accepts every $f : \{0,1\}^n \to \{0,1\}$ at relative distance at least $\varepsilon$ from all parities with probability at most $(1 - \varepsilon)^k$. Conversely, three queries are necessary for one-sided testing: every decision tree of depth at most two that accepts all parities accepts every function $f$ with $f(0) = 0$; so a one-sided linearity tester that rejects, with positive probability, some function $f$ with $f(0) = 0$ must make at least three queries on some random string.

## Proof sketch

BLR soundness gives rejection probability at least the distance $\varepsilon$ per round; independent rounds multiply acceptance. For the lower bound, the at most two points queried along $f$'s path, together with $0$, are consistent with some parity (any two nonzero points and their values extend to a linear function when $f(0) = 0$), which follows the same path and reaches the same accepting leaf.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Proof depends on

- [Acceptance probability of the BLR test in Fourier form](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-accept-prob-eq.md)
- [Independent repetition multiplies acceptance probabilities](../../../TheoryOfComputation/pcp-and-inapproximability/pcp-verifiers-and-local-tests/independent-repetition-of-local-tests.md)

## Sources

- M. Blum, M. Luby and R. Rubinfeld, "Self-Testing/Correcting with Applications to Numerical Problems", Journal of Computer and System Sciences 47(3), 1993.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
