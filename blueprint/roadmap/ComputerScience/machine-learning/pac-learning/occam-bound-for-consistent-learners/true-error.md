# True error against a target labelling

Let $\mu$ be a measure on a measurable space $X$ of instances (a probability distribution in the
intended use), $c : X \to Y$ a target labelling and $h : X \to Y$ a hypothesis. The true error of $h$
against $c$ is

$$\operatorname{err}_\mu(h) = \mu\{x \in X : h(x) \ne c(x)\} \in [0, \infty],$$

the measure of the disagreement set, taken as an outer measure when that set is not measurable. For a
probability distribution $\mu$ it is the probability (or outer probability) that $h$ disagrees with the
target on a fresh instance; Shalev-Shwartz and Ben-David write it $L_{(\mathcal{D}, f)}(h)$. When $c$ and
the disagreement set are measurable, it is the 0-1 error of $h$ under the joint distribution obtained
by labelling $\mu$ with $c$ ([the bridge to the labelled distribution](true-error-eq-error-map.md)).

Valiant's 1984 definition is one-sided: examples are drawn from a distribution on the positive
examples only, and the hypothesis must imply the target. Its two-sided variant, sketched in the
same section, measures errors on both sides, as here.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 3.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Chapter 2, equation (2.1).
