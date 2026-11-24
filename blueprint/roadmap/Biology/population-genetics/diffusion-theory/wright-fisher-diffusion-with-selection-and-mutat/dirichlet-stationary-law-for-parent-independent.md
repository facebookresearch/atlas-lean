# The Dirichlet law is stationary for parent-independent mutation

Let $\theta > 0$ and let $\nu$ be a probability vector on $K \ge 2$ alleles with all $\nu_i > 0$. For the neutral
[K-allele generator](k-allele-wright-fisher-generator-on-the-simplex.md) with parent-independent mutation, $L f = \frac12 \sum_{i,j} x_i(\delta_{ij} - x_j)\partial_i\partial_j f + \frac\theta2 \sum_i (\nu_i - x_i)\partial_i f$,
the Dirichlet law $\pi = \mathrm{Dirichlet}(\theta\nu_1, \dots, \theta\nu_K)$ on the simplex satisfies

$$\int L f \, d\pi = 0$$

for every twice continuously differentiable $f$. For a monomial $x^n = \prod_i x_i^{n_i}$, with $|n| = \sum_i n_i$ and $c_i = \theta\nu_i$,

$$L x^n = \frac12 \sum_{i:\,n_i\ge1} n_i (n_i - 1 + c_i)\, x^{n - e_i} - \frac12 |n| (|n| - 1 + \theta)\, x^n,$$

and the Dirichlet moments $\mathbb E\, x^n = \prod_i (c_i)_{(n_i)} / \theta_{(|n|)}$ give $\mathbb E\, x^{n - e_i} = \mathbb E\, x^n\, (\theta + |n| - 1)/(c_i + n_i - 1)$ for each $i$ with $n_i\ge1$, so
$\mathbb E\, L x^n = \frac12 \mathbb E\, x^n\, (\theta + |n| - 1)\bigl(\sum_{i:\,n_i\ge1} n_i - |n|\bigr) = 0$; polynomials approximate every twice continuously
differentiable function together with its first and second derivatives uniformly on the simplex, and $L$ has bounded
coefficients there. For $K = 2$ this is the stationarity of the
[Beta density](../wright-fisher-diffusion-with-mutation/flux-beta-pdfreal.md) $\mathrm{Beta}(\theta\nu_1, \theta\nu_2)$, and the laws for all $K$ are the finite-dimensional marginals of the
[Dirichlet-process stationary law](../fleming-viot-processes/dirichlet-process-stationary-law.md) of the Fleming–Viot diffusion.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](k-allele-wright-fisher-generator-on-the-simplex.md)
- [Zero probability flux of the Beta density](../wright-fisher-diffusion-with-mutation/flux-beta-pdfreal.md)
- [Dirichlet-process stationary law of the Fleming–Viot process](../fleming-viot-processes/dirichlet-process-stationary-law.md)

## Sources

- P. A. Jenkins and D. Spanò, "Exact simulation of the Wright–Fisher diffusion", Annals of Applied Probability 27 (2017), 1478–1509, <https://doi.org/10.1214/16-AAP1236>; preprint <https://arxiv.org/abs/1506.06998>, Section 2, display after equation (9) (the parent-independent Fleming–Viot diffusion is reversible with the Dirichlet process as stationary law, whose finite-dimensional distributions are Dirichlet). The generator identity is derived above.
