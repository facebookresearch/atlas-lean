# Pure differential privacy is preserved by randomized post-processing

If $M$ is [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$ and $k$ assigns to every output $a$ a probability mass function $k(a)$, then the mechanism $d \mapsto \sum_a M(d)(a)\, k(a)$ is $\varepsilon$-differentially private for $\mathrm{adj}$. The kernel $k$ may depend on the released value but not on the database.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Proposition 2.1.
