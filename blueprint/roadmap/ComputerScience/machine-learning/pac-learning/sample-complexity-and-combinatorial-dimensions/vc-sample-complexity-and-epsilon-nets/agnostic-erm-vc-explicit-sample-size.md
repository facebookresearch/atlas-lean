# Agnostic PAC learning of finite VC classes by ERM with explicit sample size

Let $C$ be a class of functions $X \to \{0,1\}$ on a countable domain $X$ with measurable singletons, and let every finite set shattered by $C$ have at most $d$ points. For every distribution $D$ on $X \times \{0,1\}$, every empirical risk minimizer $A$ for $C$ (0-1 loss) on $m$ i.i.d. examples satisfies

$$
D^m\big(\mathrm{err}_D(A(S)) > \inf_{c \in C} \mathrm{err}_D(c) + \varepsilon\big) \le 4\,\Pi_C(2m)\, e^{-m\varepsilon^2/32}.
$$

Hence for $\varepsilon, \delta \in (0,1)$ every ERM is an agnostic $(\varepsilon, \delta)$-PAC learner from

$$
m \ge \frac{64}{\varepsilon^2}\Big(2d \ln\frac{20}{\varepsilon} + \ln\frac{4}{\delta}\Big)
$$

examples, and $C$ has the uniform convergence property with threshold $\lceil (16/\varepsilon^2)(2\,\mathrm{VCdim}(C)\ln(10/\varepsilon) + \ln(4/\delta)) \rceil$.

## Proof sketch

Apply the Vapnik-Chervonenkis inequality at accuracy $\varepsilon/2$: on an $\varepsilon/2$-representative sample every empirical risk minimizer is within $\varepsilon$ of the best error in the class. Sauer's lemma and elementary estimates give the sample size.

## Depends on

- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Uniform convergence property and eps-representative samples](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)
- [Growth function](../../../../not-yet-classified/growth-function/growth-function.md)

## Proof depends on

- [Vapnik-Chervonenkis inequality: uniform convergence from the growth function](vapnik-chervonenkis-inequality.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- V. N. Vapnik and A. Ya. Chervonenkis, "On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities", Theory of Probability and Its Applications, 1971.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
