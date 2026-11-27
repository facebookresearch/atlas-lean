# Consistency, delta variance and weak-denominator behavior of the f4 ratio

Let $\hat N_n,\hat D_n$ be measurable real estimators on one probability space of fixed population values $N=f_4(A,O;X,C)$ and $D=f_4(A,O;B,C)$. Define $\hat r_n=\hat N_n/\hat D_n$, with value $0$ when $\hat D_n=0$, for $n\ge1$. The regular limit is $r=N/D$; it equals an admixture proportion only under the separate structural hypotheses of [f4-ratio identification](../patterson-s-f-statistics/f4-ratio.md).

## Nonzero denominator

Suppose $D\ne0$. On $|\hat D_n-D|<|D|/2$, the estimated denominator is nonzero and

$$\left|\hat r_n-\frac ND\right|\le\frac{2}{D^2}\left(|D|\,|\hat N_n-N|+|N|\,|\hat D_n-D|\right).$$

If both estimators converge in probability, this event has probability tending to one and the bound proves $\hat r_n\to r$ in probability. If both converge almost surely, the event holds eventually almost surely and the same bound proves almost-sure convergence. Equivalently, the measurable, zero-totalized ratio map is continuous at $(N,D)$ precisely where the denominator is nonzero; its discontinuities away from that point do not affect this continuous-mapping argument.

If, in addition, the **joint** convergence

$$\sqrt n\bigl((\hat N_n,\hat D_n)-(N,D)\bigr)\ \Rightarrow\ \mathcal N_2(0,\Sigma)$$

holds, the [delta method](../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/delta-method.md) applies to the ratio map at $(N,D)$ and gives

$$\sqrt n(\hat r_n-r)\Rightarrow\mathcal N(0,\sigma^2),\qquad v=(1/D,-N/D^2),\qquad\sigma^2=v\Sigma v^{\mathsf T}.$$

Here $\Sigma$ may be singular and $\sigma^2$ may be zero, in which case the limit is the point mass at zero. Marginal asymptotic normality does not supply a joint Gaussian limit or determine this variance. No second-order limit or studentized normal limit is asserted when $\sigma^2=0$.

## Explicit iid-block specialization

Let $Z_b=(U_b,V_b)$ be iid square-integrable real block vectors with mean $(N,D)$, covariance $\Sigma$, and $D\ne0$. Take $(\hat N_B,\hat D_B)=\bar Z_B=B^{-1}\sum_{b=1}^B Z_b$. The [multivariate central limit theorem](../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/exists-tendsto-in-distribution-inv-sqrt.md) supplies the joint limit above with $n=B$. Within-block dependence is allowed; independence and identical distribution are imposed on the block vectors.

For $B\ge2$, let $\bar Z_{(-b)}$ omit block $b$, and define the delete-one covariance of the **vector mean** by

$$J_B=\frac{B-1}{B}\sum_{b=1}^B(\bar Z_{(-b)}-\bar Z_B)(\bar Z_{(-b)}-\bar Z_B)^{\mathsf T}=\frac{1}{B(B-1)}\sum_{b=1}^B(Z_b-\bar Z_B)(Z_b-\bar Z_B)^{\mathsf T}.$$

The identity follows from $\bar Z_{(-b)}-\bar Z_B=-(Z_b-\bar Z_B)/(B-1)$. Thus $B J_B$ is the unbiased sample covariance of the block vectors, not $J_B$ itself. The strong law applied to the coordinates and their products gives $B J_B\to\Sigma$ almost surely. The product moments are integrable by Cauchy–Schwarz; explicitly, entry $(i,j)$ equals $B/(B-1)$ times the difference between the sample average of $Z_{b,i}Z_{b,j}$ and the product of the sample coordinate means.

The plug-in gradient $\hat v_B=(1/\hat D_B,-\hat N_B/\hat D_B^2)$, set to zero at a zero denominator, therefore gives $\hat\sigma_B^2=\hat v_B(BJ_B)\hat v_B^{\mathsf T}\to\sigma^2$ almost surely. If $\sigma^2>0$, division by $\sqrt{\hat\sigma_B^2}$ yields a standard-normal limit for $\sqrt B(\hat r_B-r)$; define the standardized statistic to be zero on the exceptional event $\hat\sigma_B^2=0$, whose probability tends to zero. Positive definiteness of the entire $\Sigma$ is not needed for this scalar conclusion.

This is an equal-weight iid-block model and a vector-covariance delta estimate. It is not a proof for arbitrary linked loci, unequal block weights or the nonlinear delete-one jackknife of the ratio itself. For dependent loci, a suitable joint CLT and consistency of the chosen covariance estimator remain separate hypotheses. Merely calling a procedure a block jackknife does not establish either hypothesis.

## Zero and near-zero denominators

For $D=0$, take a standard normal $Z$, $\hat N_n=N\ne0$, and $\hat D_n=Z/\sqrt n$. Both estimators are consistent, but for every $M>0$,

$$\Pr(|\hat r_n|\le M)=\Pr\!\left(|Z|\ge\frac{|N|\sqrt n}{M}\right)\longrightarrow0.$$

Hence $|\hat r_n|\to\infty$ in probability. For each finite $n$, the denominator density is continuous and strictly positive near zero, so integrating $1/|x|$ against it diverges. Both the positive and negative parts of $\hat r_n$ have infinite expectations: $\mathbb E|\hat r_n|=\infty$ and its ordinary signed mean is undefined, not a principal-value zero. The value assigned on the probability-zero event $\hat D_n=0$ changes none of these conclusions. A totalized real integral of a nonintegrable function must not be interpreted as a finite probabilistic expectation.

A fixed, small **nonzero** $D$ still permits the preceding pointwise consistency and delta limit. The constants in the error bound and gradient become ill-conditioned as $D$ approaches zero; they do not provide uniform control there. For an explicit local-to-zero example, put $D_n=c/\sqrt n$, $N_n=\alpha D_n$ with $c\ne0$, and take independent standard normals $Z_N,Z_D$. The estimators $(\alpha c+Z_N)/\sqrt n$ and $(c+Z_D)/\sqrt n$ have errors tending to zero, but their ratio has the same nondegenerate law $(\alpha c+Z_N)/(c+Z_D)$ for every $n$, and need not concentrate at $\alpha$.

Mean existence is a separate issue even away from zero: $\hat N_n=N\ne0$, $\hat D_n=D+Z/\sqrt n$ with fixed $D\ne0$ gives a consistent ratio but still has no finite-sample signed mean, since its denominator density is positive at zero. Conversely, zero population numerator and denominator do not force divergence: if $\hat N_n=\alpha\hat D_n$ and $\hat D_n=Z/\sqrt n$, the ratio equals $\alpha$ almost surely.

## Depends on

- [f4-ratio estimation of the admixture proportion](../patterson-s-f-statistics/f4-ratio.md)

## Proof depends on

- [Delta method](../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/delta-method.md)
- [Multivariate central limit theorem with a constructed limit](../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/exists-tendsto-in-distribution-inv-sqrt.md)

## Sources

- N. Patterson et al., *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3522152/>, f4-ratio estimation, equations (4)–(5), and the D-statistics discussion of weighted block jackknife errors. This motivates the statistical application; the explicit assumptions, iid equal-weight specialization, probability proofs and counterexamples above are mathematical derivations, not a theorem in that paper for arbitrary dependent loci.
