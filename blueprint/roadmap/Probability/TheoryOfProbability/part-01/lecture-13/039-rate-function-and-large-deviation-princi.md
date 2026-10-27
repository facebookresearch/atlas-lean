---
article_id: af_691ca7b0ea6b777317f2a892
declaration: structure
origin: cited
statement: formalized
lean: SatisfiesLDP
---

# Definition (rate function and large deviation principle)

The rate function is a lower-semicontinuous map $I \colon \mathcal{X} \to [0, \infty]$ (the sets $\{x : I(x) \leq a\}$ are closed; the rate function is called "good" if these sets are compact). $\{\mu_n\}$ satisfy the LDP with rate function $I$ and speed $n$ if for all $\Gamma \in \mathcal{B}$, $$-\inf_{x \in \Gamma^{\circ}} I(x) \leq \liminf_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \leq \limsup_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \leq -\inf_{x \in \overline{\Gamma}} I(x).$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 13, General large deviation principle section](../../../../../sources/v1/TheoryOfProbability.md)
