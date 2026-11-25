# Properties of the distribution function of a random variable

Let $X$ be a real random variable on a probability space $(\Omega, \mathcal F, P)$, and let
$F(x) = P(X \le x)$, $x \in \mathbb R$, be its distribution function. Then:

1. $F$ is nondecreasing;
2. $\lim_{x \to \infty} F(x) = 1$ and $\lim_{x \to -\infty} F(x) = 0$;
3. $F$ is right-continuous: $\lim_{y \downarrow x} F(y) = F(x)$ for every $x \in \mathbb R$.

## Proof

If $x \le y$ then $\{X \le x\} \subseteq \{X \le y\}$, so $F(x) \le F(y)$ by monotonicity of $P$. Since $F$ is monotone,
each limit can be computed along a monotone sequence. As $y \downarrow x$ the events $\{X \le y\}$ decrease to
$\{X \le x\}$, and as $x \downarrow -\infty$ the events $\{X \le x\}$ decrease to $\emptyset$, so continuity of $P$ from
above gives right-continuity and the limit $0$. As $x \uparrow \infty$ they increase to $\Omega$, and continuity of $P$
from below gives the limit $P(\Omega) = 1$.

## Depends on

- [Probability measure](../../../foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Continuity from above of a finite measure, real-valued form](../../../correlation-inequalities/harris-fkg-bk/harris-inequality/ih-tendsto-measure-real-i-inter.md)
- [Continuity from below for increasing families of sets](../../../../MeasureTheory/measures/measures-and-countable-additivity/continuity-of-measures/tendsto-measure-i-union-at-top.md)
- [Monotonicity of a measure](../../../../MeasureTheory/measures/measures-and-countable-additivity/measures/measure-mono.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 1.2.1, parts (i)–(iii) (version read: the author's January 2019 PDF).
