# Spectrum and weighted degree string kernels

Let $\Sigma$ be a finite alphabet (nucleotides or amino acids) and $x, x' \in \Sigma^*$ sequences.

**Spectrum kernel.** For $\ell \ge 1$ let $\Phi_\ell(x) \in \mathbb N^{\Sigma^\ell}$ have coordinate $\Phi_\ell(x)_s$ equal to the number of occurrences of the $\ell$-mer $s$ in $x$. The $\ell$-spectrum kernel is

$$k^{\mathrm{spec}}_\ell(x, x') = \langle \Phi_\ell(x), \Phi_\ell(x') \rangle = \sum_{s \in \Sigma^\ell} \Phi_\ell(x)_s\, \Phi_\ell(x')_s,$$

and the mixed spectrum kernel with nonnegative weights $\beta_1, \dots, \beta_\ell$ is $k^{\mathrm{mix}}_\ell = \sum_{d=1}^{\ell} \beta_d\, k^{\mathrm{spec}}_d$.

**Weighted degree kernel.** For sequences of a common length $L$, with $x[l : l + d]$ the substring of length $d$ starting at position $l$,

$$k^{\mathrm{WD}}_\ell(x, x') = \sum_{d=1}^{\ell} \beta_d \sum_{l=1}^{L - d + 1} \mathbf 1\big\{x[l : l + d] = x'[l : l + d]\big\}, \qquad \beta_d = \frac{2(\ell - d + 1)}{\ell(\ell + 1)},$$

the suggested weights decreasing linearly in $d$ and summing to $1$.

**Properties.**

1. Each kernel is positive semidefinite: $k^{\mathrm{spec}}_\ell$ is an explicit inner product; $k^{\mathrm{WD}}_\ell$ is the inner product of the feature maps $x \mapsto \big(\sqrt{\beta_d}\,\mathbf 1\{x[l : l + d] = s\}\big)_{d, l, s}$; nonnegative combinations of positive semidefinite kernels are positive semidefinite.
2. The weighted degree kernel equals a mixed spectrum kernel applied separately at each position (up to boundary effects): it rewards shared substrings only when they occur at the same position, as a position weight matrix does, whereas the spectrum kernel is invariant to where a $k$-mer occurs.
3. Although the feature space of $k^{\mathrm{spec}}_\ell$ has dimension $|\Sigma|^\ell$, the kernel can be evaluated in time linear in $|x| + |x'|$ because only $\ell$-mers occurring in the sequences contribute (for example by sorting or hashing their $\ell$-mers, or with suffix structures).
4. Composition with a polynomial kernel, $(k^{\mathrm{spec}}_\ell(x, x') + \kappa)^{p}$ with $\kappa \ge 0$, yields features that are products of up to $p$ $\ell$-mer counts, i.e. co-occurrences of up to $p$ $\ell$-mers, and remains positive semidefinite.

## Expansion

Positive semidefiniteness of an explicit inner product is $\sum_{a,b} c_a c_b \langle \Phi(x_a), \Phi(x_b)\rangle = \|\sum_a c_a \Phi(x_a)\|^2 \ge 0$. The weights $\beta_d$ sum to $\frac{2}{\ell(\ell+1)}\sum_{d=1}^{\ell}(\ell - d + 1) = 1$; the decreasing weights compensate for the fact that a matching substring of length $d$ also produces matches of all its shorter substrings. Exact $k$-mer matching becomes rare for large $\ell$, which degrades the plain spectrum kernel, while the mixed and weighted degree kernels keep contributions from shorter matches. In the source's splice-site recognition example, adding positional information (weighted degree kernel) markedly improved accuracy over the spectrum kernel, and since polynomial and Gaussian kernels are functions of a base inner product, sequence kernels can be plugged into them to obtain more complex decision boundaries.

## Sources

- A. Ben-Hur, C. S. Ong, S. Sonnenburg, B. Schölkopf, G. Rätsch, "Support vector machines and kernels for computational biology", PLoS Computational Biology (2008), sections "Kernels describing ℓ-mer content" (spectrum and mixed spectrum kernels, Eqs. (11)–(12)), "Kernels using positional information" (weighted degree kernel, Eq. (13)) and "Kernels for real-valued data" (polynomial kernel, Eq. (9)), <https://doi.org/10.1371/journal.pcbi.1000173> (PMC2547983).
