# Large deviation principle for a sequence of measures

Let $X$ be a topological space with
a $\sigma$-algebra containing every open set, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence of
measures on $X$, and let $I : X \to [0, \infty]$. The sequence $(\mu_n)$ satisfies the large
deviation principle with rate function $I$ and speed $n$ if $I$ is a rate function, every open
set $U \subseteq X$ satisfies

$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(U) \ge -\inf_{x \in U} I(x),$$

and every closed set $F \subseteq X$ satisfies

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(F) \le -\inf_{x \in F} I(x).$$

Here $\log 0 = -\infty$, an infimum over the empty set is $\infty$, and the limits are taken in
the extended reals.

Varadhan's definition also asks the rate function to be good (compact sub-level sets), and in his
2008 survey he remarks that this is not needed for the bounds themselves but lets one reduce the
analysis to compact sets. Here goodness is the separate hypothesis
[good rate function](is-good-rate-function.md), assumed exactly where a result needs it: the
[contraction principle](../contraction-principle/satisfies-ldp-map.md),
[superexponential tightness](../superexponential-tightness-and-product-ldps/exists-is-compact-measure-compl-le.md)
and the [product principle](../superexponential-tightness-and-product-ldps/satisfies-ldp-prod.md).
[Varadhan's integral lemma](../varadhan-s-integral-lemma/tendsto-log-lintegral-exp.md) and the
[tilted principle](../tilted-large-deviation-principle/satisfies-ldp-tilted-measure.md) hold
without it.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 2 (definition of a rate function and of the LDP) (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).
- S. R. S. Varadhan, "Large deviations", *Ann. Probab.* 36 (2008), 397–419, Section 1, conditions (1)–(3) (arXiv:0804.2330).
