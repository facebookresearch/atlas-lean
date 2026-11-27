# Martingale problem for the Wright-Fisher diffusion with selection and two-way mutation

Let $\alpha\in\mathbb R$ and $\theta_1,\theta_2\ge0$. Use the
[selection-mutation generator](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)

$$L_{\alpha,\theta}f(x)=\tfrac12x(1-x)f''(x)
 +\left(\alpha x(1-x)+\tfrac12[\theta_1(1-x)-\theta_2x]\right)f'(x).$$

On a filtered probability space $(\Omega,\mathcal F,\mathbb P,(\mathcal F_t)_{t\ge0})$,
a process $X:[0,\infty)\times\Omega\to\mathbb R$ solves this martingale problem
if it takes values in $[0,1]$, has continuous paths, is adapted, and for every
$f:\mathbb R\to\mathbb R$ of class $C^2$ the process

$$f(X_t)-f(X_0)-\int_0^t L_{\alpha,\theta}f(X_s)\,ds$$

is an $(\mathcal F_t)$-martingale under $\mathbb P$. In this definition,
state membership and continuity hold for every sample point, as in the
[selection-only solution notion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md).
This is a definition, not an assertion that a solution exists or is unique.
For $\theta_1=\theta_2=0$ it reduces to that solution notion on the same
probability space with selection coefficient $\alpha$.

In the diploid Wright-Fisher scaling with $N$ individuals and $M=2N$ gene
copies, a unit of time is $M$ generations, $\alpha=Ms$ and
$\theta_i=2Mu_i$. Here $\theta_1$ is towards the counted allele and
$\theta_2$ away from it. The displayed generator fixes the normalization
independently of this interpretation.

If $\theta_1>0$, the constant path $X_t=0$ is not a solution: the test
$f(x)=x$ would give the deterministic process $-\theta_1t/2$, whose
expectation differs from its initial value at every $t>0$.

## Depends on

- [Generator with selection and two-way mutation](../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)
- [Selection-only solution notion, for the zero-mutation comparison](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)

## Sources

- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 7.5, equations (7.20) and (7.24), for the two one-way generator conventions. The two-way martingale-problem formulation is stated directly using the linked generator and the selection-only solution notion.
