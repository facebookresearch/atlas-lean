# Sanov's theorem for finite alphabets

Let $Q \ge 0$ be a function on a finite alphabet $\alpha$ (a probability vector in the intended use, so that
$Q^n\{\cdot\}$ below is a probability) and $\Gamma$ a set of functions $\alpha \to \mathbb R$.
Suppose that $r \le D(P\|Q)$ for every probability vector $P \in \Gamma$ with $P \ll Q$, and that
there are $n$-types $s_n$ such that, **for all large $n$**, $s_n \in \Gamma$ and $P_{s_n} \ll Q$, and
$D(P_{s_n}\|Q) \to r$. Then $r = D(\Gamma\|Q)$, the infimum over the distributions in $\Gamma$, and

$$\frac1n \log Q^n\{x \in \alpha^n : P_x \in \Gamma\} \longrightarrow -r \qquad (n \to \infty),$$

natural logarithm, where $Q^n\{\cdot\}$ is the [product weight](iid-prob.md); it is positive for large $n$.

Comparison with the sources. Csiszár (1998) assumes (III.21),
$\lim_n D(\Gamma \cap \mathcal P_n \| Q) = D(\Gamma \| Q)$, a condition on large $n$ only. When
$D(\Gamma\|Q) < \infty$ the hypothesis above is equivalent to it: (III.21) makes $\Gamma \cap \mathcal P_n$
contain a type of finite divergence for every large $n$, and since $\Gamma \cap \mathcal P_n$ is finite
one can take $s_n$ to be a minimiser; conversely $D(\Gamma\|Q) \le D(\Gamma \cap \mathcal P_n\|Q) \le
D(P_{s_n}\|Q) \to r = D(\Gamma\|Q)$. The case $D(\Gamma\|Q) = \infty$, where the source's limit is
$-\infty$, is covered only by the [upper bound](eventually-iid-prob-empirical-mem-le.md), which then
holds for every $r$. The hypothesis may fail for small $n$: for instance
$\Gamma = \{P : P(\mathrm{true}) \in [2/5, 9/20]\}$ on $\{\mathrm{true}, \mathrm{false}\}$ contains no
$1$-type and no $2$-type, and the theorem applies to it. Csiszár–Shields (2004) assume instead that
$\Gamma$ is the closure of its interior and $Q$ is strictly positive, which implies (III.21).

The proof is the method of types: the [union of type classes](iid-prob-empirical-mem-eq-sum.md),
the [non-asymptotic upper bound](iid-prob-empirical-mem-le.md) and the
[non-asymptotic lower bound](exp-le-pow-mul-iid-prob-empirical-mem.md), with the
[subexponential number of types](eventually-pow-card-le-exp.md).

## Background

- [Sanov's theorem](../../../Probability/large-deviations/sanov-s-theorem/satisfies-ldp-sample-empirical-measure.md):
  the large deviation principle for empirical measures on a Polish space (Varadhan's notes), of which
  this is the finite-alphabet case in the form Csiszár proves by counting.
- [Large deviations](../../../Probability/large-deviations/README.md): rate functions and the
  general principles; on a finite alphabet the rate $D(\cdot\|Q)$ is continuous on the simplex when
  $Q > 0$, and in general on the distributions supported in the support of $Q$.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Theorem III.3, (III.22).
- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Theorem 2.1.
