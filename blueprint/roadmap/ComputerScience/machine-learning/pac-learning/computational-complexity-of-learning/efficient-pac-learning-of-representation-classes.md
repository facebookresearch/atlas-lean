# Efficient PAC learning of representation classes

Let $C = \bigcup_n C_n$ be a representation class of Boolean functions on $X_n = \{0,1\}^n$ with a size measure
$\mathrm{size}(c)$. An algorithm efficiently PAC learns $C$ if, given $\varepsilon, \delta \in (0,1)$, $n$, a size bound
$s$ and access to an oracle returning independent examples $(x, c(x))$ with $x \sim D$, for every distribution $D$
on $X_n$ and every target $c \in C_n$ with $\mathrm{size}(c) \le s$, it outputs with probability at least
$1 - \delta$ a hypothesis of error at most $\varepsilon$, runs in time polynomial in $n$, $s$, $1/\varepsilon$ and
$1/\delta$, and outputs a hypothesis that can be evaluated on any $x \in X_n$ in time polynomial in the same
parameters. The learner is proper if its hypotheses belong to $C$ and improper otherwise.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [The 0-1 loss as an abstract loss](../risk-of-the-0-1-loss/zero-one-loss.md)

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27(11) (1984) 1134–1142: the learning protocol with an example oracle and polynomial-time learnability. <http://web.mit.edu/6.435/www/Valiant84.pdf>
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Chapter 8 (the runtime of learning; efficient learnability and its dependence on the representation). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
