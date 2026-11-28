# Agnostic multiclass PAC learning from finite Natarajan dimension

Let $X$ be countable with measurable singletons, $\beta$ a finite label set with $k \ge 2$ elements, and $C$ a class of functions $X \to \beta$ with Natarajan dimension $d$. There is an absolute constant $C_2 > 0$ such that

1. for $d \ge 1$, $C$ has the uniform convergence property with sample complexity $m^{\mathrm{UC}}_C(\varepsilon, \delta) \le C_2 \frac{d \log k + \log(1/\delta)}{\varepsilon^2}$;
2. $C$ is agnostically PAC learnable with sample complexity $m_C(\varepsilon, \delta) \le C_2 \frac{d \log k + \log(1/\delta)}{\varepsilon^2}$ (Shalev-Shwartz and Ben-David, Theorem 29.3, items 1 and 2, upper bounds), and every empirical risk minimizer is an agnostic PAC learner from $m^{\mathrm{UC}}_C(\varepsilon/2, \delta)$ examples (Corollary 4.4).

## Proof sketch

The upper bounds follow from Natarajan's lemma, which bounds the number of labelings $C$ realizes on a finite set, along the lines of the proof of the fundamental theorem for binary classes (Shalev-Shwartz and Ben-David, Section 29.2.1).

Derived (not stated in the cited sources, which give only absolute constants): if $C$ N-shatters no finite set of more than $d$ points, the Boolean loss class of $C$ shatters no finite set of more than $6d(\ln k + 1)$ labelled points, since a shattered set of $n$ labelled points realizes $2^n$ loss patterns while Natarajan's lemma with $\sum_{i \le d}\binom{n}{i}\binom{k}{2}^i \le e^{n/3}(3k^2)^d$ bounds them. Feeding this VC bound into the chaining uniform convergence bound gives explicit sample sizes: $m \ge (98304\, d(\ln k + 1) + 32\ln(4/\delta))/\varepsilon^2$ i.i.d. examples are $\varepsilon$-representative with probability at least $1-\delta$, and every empirical risk minimizer is an agnostic $(\varepsilon, \delta)$-PAC learner from $m \ge (393216\, d(\ln k + 1) + 128 \ln(4/\delta))/\varepsilon^2$ examples.

## Depends on

- [Multiclass fundamental theorem (Natarajan bounds)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/multiclass-fundamental-theorem.md)
- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Natarajan's lemma](natarajans-lemma.md)

## Proof depends on

- [Sharp agnostic sample complexity of VC classes by chaining](../vc-sample-complexity-and-epsilon-nets/sharp-agnostic-vc-rate-by-chaining.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Corollary 4.4 and Theorem 29.3.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
