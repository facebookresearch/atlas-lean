---
article_id: af_49e5b04e90c282f103266b12
declaration: theorem
origin: cited
statement: formalized
lean: markov_property_full
---

# Theorem (Markov property)

Take $(\Omega_0, \mathcal{F}) = (S^{\{0,1,\ldots\}}, \mathcal{S}^{\{0,1,\ldots\}})$, and let $P_\mu$ be the Markov chain measure and $\theta_n$ the shift operator on $\Omega_0$. If $Y \colon \Omega_0 \to \mathbb{R}$ is bounded and measurable then $E_\mu(Y \circ \theta_n \mid \mathcal{F}_n) = E_{X_n} Y$.

## Depends on

- [Definition (Conditional expectation)](../../part-01/lecture-25/053-conditional-expectation.md)
- [Definition (Markov chain, general)](../lecture-30/084-markov-chain-general.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 31, Markov properties section](../../../../../sources/v1/TheoryOfProbability.md)
