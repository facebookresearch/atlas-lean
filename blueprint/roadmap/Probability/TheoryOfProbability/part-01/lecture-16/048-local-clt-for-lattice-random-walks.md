---
article_id: af_f420af2768e8c3f24c5169a1
declaration: theorem
origin: cited
lean: ProbabilityTheory.local_clt_lattice
---

# Theorem (Local CLT for lattice random walks)

Assume $X_i$ are i.i.d. lattice random variables with $E[X_i] = 0$ and $E[X_i^2] = \sigma^2 \in (0, \infty)$, supported on $b + h\mathbb{Z}$. Write $p_n(x) = P(S_n / \sqrt{n} = x)$ for $x \in \mathcal{L}_n \coloneqq (nb + h\mathbb{Z}) / \sqrt{n}$ and $n(x) = (2\pi\sigma^2)^{-1/2} \exp(-x^2 / 2\sigma^2)$. Then as $n \to \infty$, $\sup_{x \in \mathcal{L}_n} |n^{1/2} / h \cdot p_n(x) - n(x)| \to 0$.

## Depends on

- [Definition (lattice random variable)](046-lattice-random-variable.md)

## Proof depends on

- [Definition (characteristic function)](../lecture-8/019-characteristic-function.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 16, section on local limit theorems for walks on Z (also recalled in Lecture 17)](../../../../../sources/v1/TheoryOfProbability.md)
