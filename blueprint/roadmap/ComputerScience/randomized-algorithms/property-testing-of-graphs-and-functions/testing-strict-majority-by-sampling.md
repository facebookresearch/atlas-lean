# Testing strict majority by sampling

Let $L$ be the set of binary strings in which ones form a strict majority, and let $x$ either belong to $L$ or be $\varepsilon$-far from $L$ (more than $\varepsilon|x|$ bits must change to enter $L$). The tester that samples $O(1/\varepsilon^2)$ positions independently and uniformly (with replacement) and accepts iff the observed fraction of ones exceeds $1/2 - \varepsilon/2$ accepts members with probability at least $2/3$ and rejects strings $\varepsilon$-far from $L$ with probability at least $2/3$; it runs in time polynomial in the logarithm of the input length given direct access.

## Proof sketch

Members have density above $1/2$; strings $\varepsilon$-far have density at most $1/2 - \varepsilon$ (otherwise changing few zeros to ones reaches a strict majority). Hoeffding's inequality separates the two densities with $O(1/\varepsilon^2)$ samples.

## Depends on

- [Local test on a proof string](../../../TheoryOfComputation/pcp-and-inapproximability/pcp-verifiers-and-local-tests/local-test-on-a-proof-string.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
