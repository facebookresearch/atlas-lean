# Sharp agnostic sample complexity of VC classes by chaining

Let $C$ be a class of functions from a countable domain with measurable singletons to $\{0,1\}$, with the $0$-$1$ loss, of VC dimension $d < \infty$. There is an absolute constant $C_2 > 0$ such that

1. for $d \ge 1$, $C$ has the uniform convergence property with sample complexity $m^{\mathrm{UC}}_C(\varepsilon, \delta) \le C_2 \frac{d + \log(1/\delta)}{\varepsilon^2}$;
2. $C$ is agnostically PAC learnable with sample complexity $m_C(\varepsilon, \delta) \le C_2 \frac{d + \log(1/\delta)}{\varepsilon^2}$, with no logarithmic factor in $1/\varepsilon$ (Shalev-Shwartz and Ben-David, Theorem 6.8, items 1 and 2, upper bounds), and every empirical risk minimizer is an agnostic PAC learner from $m^{\mathrm{UC}}_C(\varepsilon/2, \delta)$ examples (Corollary 4.4).

## Proof sketch

The upper bound without a logarithmic factor is obtained by chaining (Vershynin, Section 8.3): symmetrize with a ghost sample as for the Vapnik-Chervonenkis inequality, but bound the fraction of bad swaps of a fixed double sample by chaining over nets of the realized labelings instead of a union bound over all restrictions.

Derived (not stated in the cited sources, which give only absolute constants): let $Z$ be a countable set with all subsets measurable, $G$ a class of functions $Z \to \{0,1\}$ whose shattered finite sets have at most $d$ points, $\mu$ a probability measure on $Z$ and $\varepsilon > 0$. Nets of the realized labelings at Hamming scales $2m/4^{n+1}$ have size at most $2^{2d(2n+5)}$ by Dudley's packing bound, and Hoeffding's inequality along the chain gives, when $16384\, d \le m\varepsilon^2$,
$\mu^m(\{S : \exists g \in G,\ |\tfrac{1}{m}\#\{i : g(S_i) = 1\} - \mu(g = 1)| \ge \varepsilon\}) \le 4 e^{-m\varepsilon^2/32}$, with no growth-function factor. Consequently, for $\delta \in (0,1)$: $m \ge (16384\, d + 32 \ln(4/\delta))/\varepsilon^2$ examples are $\varepsilon$-representative for $C$ with probability at least $1 - \delta$; if $65536\, d \le m\varepsilon^2$, every empirical risk minimizer misses $\inf_{c \in C}\mathrm{err}_D(c) + \varepsilon$ with probability at most $4e^{-m\varepsilon^2/128}$; and every ERM is an agnostic $(\varepsilon, \delta)$-PAC learner from $m \ge (65536\, d + 128 \ln(4/\delta))/\varepsilon^2$ examples. The same holds for any concept class (any label set) whose Boolean loss class shatters no finite set of more than $d$ labelled points.

## Depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/vc-classes-have-uniform-convergence.md)
- [Uniform convergence property and eps-representative samples](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)
- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Double-sample symmetrization: ghost samples and coordinate swaps](double-sample-symmetrization.md)
- [Dudley's packing bound for classes of bounded VC dimension](../packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Corollary 4.4 and Theorem 6.8.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
