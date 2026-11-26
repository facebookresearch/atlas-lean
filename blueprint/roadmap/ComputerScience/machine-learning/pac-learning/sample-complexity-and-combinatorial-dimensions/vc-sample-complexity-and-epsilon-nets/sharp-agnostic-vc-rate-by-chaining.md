# Sharp agnostic sample complexity of VC classes by chaining

Let $Z$ be a countable set with all subsets measurable and let $G$ be a class of functions $Z \to \{0,1\}$ such that every finite set shattered by $G$ has at most $d$ points.
Let $\mu$ be a probability measure on $Z$ and $\varepsilon > 0$. If $16384\, d \le m\varepsilon^2$, then

$$
\mu^m\Big(\Big\{S : \exists g \in G,\ \Big|\tfrac{1}{m}\#\{i : g(S_i) = 1\} - \mu(g = 1)\Big| \ge \varepsilon\Big\}\Big) \le 4\, e^{-m\varepsilon^2/32},
$$

with no growth-function factor. Consequently, for a binary class $C$ on a countable domain with measurable singletons whose shattered finite sets have at most $d$ points, and $\delta \in (0,1)$:

1. $m \ge (16384\, d + 32 \ln(4/\delta))/\varepsilon^2$ i.i.d. examples are $\varepsilon$-representative for $C$ with probability at least $1 - \delta$;
2. if $65536\, d \le m\varepsilon^2$, every empirical risk minimizer misses $\inf_{c \in C}\mathrm{err}_D(c) + \varepsilon$ with probability at most $4e^{-m\varepsilon^2/128}$, under every distribution $D$;
3. every ERM is an agnostic $(\varepsilon, \delta)$-PAC learner from $m \ge (65536\, d + 128 \ln(4/\delta))/\varepsilon^2$ examples, so the agnostic sample complexity is $O((d + \ln(1/\delta))/\varepsilon^2)$.

The same holds for any concept class (any label set) whose Boolean loss class shatters no finite set of more than $d$ labelled points.

## Proof sketch

Symmetrize with a ghost sample as for the Vapnik-Chervonenkis inequality, but bound the fraction of bad swaps of a fixed double sample by chaining instead of a union bound over restrictions: nets of the realized labelings at Hamming scales $2m/4^{n+1}$ have size at most $2^{2d(2n+5)}$ by Dudley's packing bound, and Hoeffding's inequality along the chain gives a fraction at most $2e^{-m\varepsilon^2/32}$ once $16384\,d \le m\varepsilon^2$. The ERM statements follow at accuracy $\varepsilon/2$.

## Depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/vc-classes-have-uniform-convergence.md)
- [Uniform convergence property and eps-representative samples](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)
- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Double-sample symmetrization: ghost samples and coordinate swaps](double-sample-symmetrization.md)
- [Dudley's packing bound for classes of bounded VC dimension](../packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
