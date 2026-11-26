# Security against adversaries with advice (nonuniform security)

An *adversary with advice* is a pair $(A, \alpha)$ where $A$ is a probabilistic polynomial-time machine and $\alpha = (\alpha_n)$ is a sequence of advice strings with $|\alpha_n| \le p(n)$ for a polynomial $p$; at parameter $n$ the adversary runs $A(1^n, \alpha_n, \cdot)$. A security game (a family of experiments with negligible-advantage requirement) is *nonuniformly secure* if every adversary with advice has negligible advantage. This is equivalent to security against families of polynomial-size circuits. Nonuniform security implies uniform security (take empty advice); the converse is not known in general.

## Depends on

- [Probabilistic polynomial-time Turing machines](../asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../asymptotic-security/negligible-adv.md)
- [Evaluation of a flat Boolean circuit](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/circuit-eval.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
