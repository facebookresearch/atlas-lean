# Pure differential privacy is preserved by deterministic post-processing

If $M$ is [$\varepsilon$-differentially private](is-dp.md) for a relation $\mathrm{adj}$, then for every function $g$ on outputs the [post-processed mechanism](post-process.md) $d \mapsto g_* M(d)$ is $\varepsilon$-differentially private for the same relation. No injectivity or finiteness assumption is made on $g$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Proposition 2.1 (deterministic case).
