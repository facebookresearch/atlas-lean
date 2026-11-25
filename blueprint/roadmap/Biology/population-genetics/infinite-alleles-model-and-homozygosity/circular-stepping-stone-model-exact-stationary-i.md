# Stationary identity by descent in the circular stepping-stone model

Let $D \ge 1$ demes sit on the cycle $\mathbb Z_D$, each with $2N$ gene copies. Going back one generation, each gene escapes an
infinite-alleles mutation with probability $1 - u$ ($0 < u \le 1$), has its parental deme at offset $\xi$ with $\mathbb P(\xi = 0) = 1 - m$ and
$\mathbb P(\xi = \pm 1) = m/2$ ($0 \le m \le 1$; for $D = 2$ the two neighbors coincide, for $D = 1$ all mass is at $0$), independently for distinct
genes, and copies a uniform one of the $2N$ copies of that deme. Let $\varphi(k)$ be the probability that two distinct genes in demes at
offset $k$ are identical by descent, and $P_2$ the law of $\xi_1 - \xi_2$. Conditioning on the parents gives

$$\varphi'(k) = (1 - u)^2 \Bigl[\sum_j P_2(j - k)\, \varphi(j) + P_2(-k)\, \frac{1 - \varphi(0)}{2N}\Bigr],$$

an affine map that contracts the sup norm by $(1 - u)^2$, so the stationary $\varphi$ is unique and attracts every start. With
$\chi_j = \bigl(1 - m + m\cos(2\pi j/D)\bigr)^2$, $q = (1 - u)^2$, $c = q/(2N)$ and
$S_k = \frac1D \sum_{j=0}^{D-1} \chi_j \cos(2\pi jk/D) / (1 - q\chi_j)$, the discrete Fourier transform gives

$$\varphi(0) = \frac{c S_0}{1 + c S_0}, \qquad \varphi(k) = (1 - \varphi(0))\, c\, S_k .$$

For $D = 1$ this is the [infinite-alleles equilibrium homozygosity](eq-homozygosity.md) with $2N$ copies; for $m = 0$, $\varphi(k) = 0$ for $k \ne 0$. Monotone decrease
of $\varphi(k)$ with circular distance does not hold in general, since $1 - m + m\cos(2\pi j/D)$ is negative for some $j$ when
$m > \frac12$: for $D = 7$, $N = 2$, $m = 1$ and $u = 0.2$ the formula gives $\varphi(1) \approx 0.0070 < \varphi(2) \approx 0.0894$.

## Depends on

- [Homozygosity recursion in the infinite-alleles model](homozygosity-step.md)
- [Equilibrium homozygosity in the infinite-alleles model](eq-homozygosity.md)

## Sources

- M. Kimura and G. H. Weiss, "The stepping stone model of population structure and the decrease of genetic correlation with distance", Genetics 49 (1964), 561–576, <https://doi.org/10.1093/genetics/49.4.561>. The recursion and its Fourier solution are derived above and checked against iteration.
