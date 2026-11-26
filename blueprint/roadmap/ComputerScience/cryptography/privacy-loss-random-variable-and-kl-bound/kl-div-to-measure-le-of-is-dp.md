# Kullback–Leibler bound for a pure differentially private mechanism

Let the output space be countable with measurable singletons. If $M$ is [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$ and both $\mathrm{adj}(d, d')$ and $\mathrm{adj}(d', d)$ hold, then

$$
\mathrm{KL}\big(M(d) \,\|\, M(d')\big) \le \varepsilon\,(e^{\varepsilon} - 1).
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Lemma 3.18 (discrete case).
