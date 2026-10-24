---
article_id: af_fe41979a04fb8fbb0f86731c
declaration: theorem
origin: cited
statement: formalized
lean: strong_markov_chain
---

# Theorem (Strong Markov property)

One can replace $n$ with an a.s. finite stopping time $N$ and the function $Y$ can vary with time. Suppose that for each $n$, $Y_n \colon \Omega_0 \to \mathbb{R}$ is measurable and $|Y_n| \leq M$ for all $n$. Then $E_\mu(Y_N \circ \theta_N \mid \mathcal{F}_N) = E_{X_N} Y_N$, where the RHS means $E_x Y_n$ evaluated at $x = X_N$, $n = N$.

## Depends on

- [Definition (Stopping time)](../../part-01/lecture-23/051-stopping-time.md)
- [Definition (Conditional expectation)](../../part-01/lecture-25/053-conditional-expectation.md)

## Proof depends on

- [Theorem (Markov property)](088-markov-property.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 31, Markov properties section](../../../../../sources/v1/TheoryOfProbability.md)
