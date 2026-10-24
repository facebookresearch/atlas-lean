---
article_id: af_deebc3e44306d49779fd1827
declaration: theorem
origin: cited
lean: StrongMarkovBMGoal98.strong_markov_setIntegral_eq
---

# Strong Markov property

Let $(s, \omega) \mapsto Y_s(\omega)$ be bounded and $\mathcal{R} \times \mathcal{C}$-measurable. If $S$ is a stopping time, then for all $x \in \mathbb{R}^d$, $E_x(Y_S \circ \theta_S \mid \mathcal{F}_S) = E_{B(S)} Y_S$ on $\{S < \infty\}$, where the RHS means the function $\phi(x, t) = E_x Y_t$ evaluated at $x = B(S)$ and $t = S$.

## Depends on

- [Definition (Conditional expectation)](../../part-01/lecture-25/053-conditional-expectation.md)
- [Stopping time](100-stopping-time.md)

## Proof depends on

- [Bounded convergence theorem](../../part-01/lecture-5/009-bounded-convergence-theorem.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 39](../../../../../sources/v1/TheoryOfProbability.md)
