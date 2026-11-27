# Agnostic multiclass PAC learning from finite Natarajan dimension with explicit sample size

Let $X$ be countable with measurable singletons, $\beta$ a finite label set with $k \ge 1$ elements, and $C$ a class of functions $X \to \beta$ that N-shatters no finite set of more than $d$ points. Then the Boolean loss class of $C$ shatters no finite set of more than $6d(\ln k + 1)$ labelled points. Consequently $m \ge (98304\, d(\ln k + 1) + 32\ln(4/\delta))/\varepsilon^2$ i.i.d. examples are $\varepsilon$-representative for $C$ with probability at least $1-\delta$, and every empirical risk minimizer is an agnostic $(\varepsilon, \delta)$-PAC learner from

$$
m \ge \frac{393216\, d(\ln k + 1) + 128 \ln(4/\delta)}{\varepsilon^2}
$$

examples; so $C$ has the uniform convergence property and is agnostically PAC learnable with sample complexity $O((d \ln k + \ln(1/\delta))/\varepsilon^2)$ for $k \ge 2$.

## Proof sketch

A shattered set of $n$ labelled points realizes $2^n$ loss patterns, while Natarajan's lemma with the estimate $\sum_{i \le d}\binom{n}{i}\binom{k}{2}^i \le e^{n/3}(3k^2)^d$ bounds them; this forces $n \le 6d(\ln k + 1)$. Feeding this VC bound for the loss class into the chaining uniform convergence theorem gives the sample sizes.

## Depends on

- [Multiclass fundamental theorem (Natarajan bounds)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/multiclass-fundamental-theorem.md)
- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Natarajan's lemma](natarajans-lemma.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)
- [Sharp agnostic sample complexity of VC classes by chaining](../vc-sample-complexity-and-epsilon-nets/sharp-agnostic-vc-rate-by-chaining.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
