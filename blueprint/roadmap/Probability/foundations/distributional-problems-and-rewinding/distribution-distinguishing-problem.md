# Distribution distinguishing problem

A *distinguishing problem* over a set of observations $X$ is a pair $(D_0, D_1)$ of discrete distributions on $X$ (the null and alternative laws). For a randomized test $A : X \to \Delta(\{0,1\})$ and a hypothesis bit $c$, the *experiment* draws $x \sim D_c$ and outputs $A(x)$; the test sees only $x$, not $c$. The advantage of $A$ is $|\Pr[A(x) = 1 \mid c = 1] - \Pr[A(x) = 1 \mid c = 0]|$. Applying a deterministic map or a Markov kernel $K$ to both laws gives the problem $(D_0K, D_1K)$, and testing transformed observations is the same as testing the original observations with the composed test. The definition fixes no model of computation, encoding or resource bound; a family of problems indexed by a parameter may change the observation set with the parameter.

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
