# Testing strict majority by sampling

Let $L$ be the set of binary strings in which ones form a strict majority, and let $x$ of length $|x| \ge 4/\varepsilon$ either belong to $L$ or be $\varepsilon$-far from $L$ (more than $\varepsilon|x|$ bits must change to enter $L$). The tester that samples $O(1/\varepsilon^2)$ positions independently and uniformly (with replacement) and accepts iff the observed fraction of ones exceeds $1/2 - \varepsilon/2$ accepts members with probability at least $2/3$ and rejects strings $\varepsilon$-far from $L$ with probability at least $2/3$; it runs in time polynomial in the logarithm of the input length given direct access (Goldreich 2008, Exercise 10.9).

## Proof sketch

Members have density above $1/2$, a margin of $\varepsilon/2$ above the threshold. A string $\varepsilon$-far from $L$ has at most $\lfloor |x|/2 \rfloor - \lfloor \varepsilon|x| \rfloor$ ones (otherwise changing at most $\varepsilon|x|$ zeros to ones reaches a strict majority), so its density is at most $1/2 - \varepsilon + 1/|x| \le 1/2 - 3\varepsilon/4$ when $|x| \ge 4/\varepsilon$, a margin of $\varepsilon/4$ below the threshold. Hoeffding's inequality separates the two cases with $O(1/\varepsilon^2)$ samples.

## Depends on

- [Local test on a proof string](../../../TheoryOfComputation/pcp-and-inapproximability/pcp-verifiers-and-local-tests/local-test-on-a-proof-string.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
