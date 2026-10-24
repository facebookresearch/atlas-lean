---
article_id: af_f00a99f0a5be02527acc96bf
declaration: structure
origin: cited
statement: formalized
lean: RegularConditionalDistribution
---

# Definition (Regular conditional distribution)

Consider a probability space $(\Omega, \mathcal{F}, P)$, a measurable map $X \colon (\Omega, \mathcal{F}) \to (S, \mathcal{S})$ and $\mathcal{G} \subset \mathcal{F}$ a $\sigma$-field. Then $\mu \colon \Omega \times \mathcal{S} \to [0,1]$ is a regular conditional distribution for $X$ given $\mathcal{G}$ if: (1) For each $A$, $\omega \mapsto \mu(\omega, A)$ is a version of $P(X \in A \mid \mathcal{G})$. (2) For a.e. $\omega$, $A \mapsto \mu(\omega, A)$ is a probability measure on $(S, \mathcal{S})$.

## Depends on

- [Definition (Conditional expectation)](../lecture-25/053-conditional-expectation.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 26](../../../../../sources/v1/TheoryOfProbability.md)
