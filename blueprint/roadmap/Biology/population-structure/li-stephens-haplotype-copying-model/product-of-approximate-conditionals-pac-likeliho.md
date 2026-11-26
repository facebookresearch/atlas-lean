# The PAC likelihood is normalized but need not be exchangeable

Fix a sample size $n\ge0$ and model parameters. Let $\mathcal H$ be a finite nonempty haplotype set, and let $q_k(\cdot\mid h_1,\ldots,h_k)$ be a probability mass function on $\mathcal H$ for each ordered history of length $k<n$. The case $k=0$ is a separately specified first-haplotype law $q_0$. The product of approximate conditionals (PAC) is

$$L(h_1,\ldots,h_n)=\prod_{k=0}^{n-1}q_k(h_{k+1}\mid h_1,\ldots,h_k),\qquad L(\varnothing)=1.$$

This is a probability law on $\mathcal H^n$: all factors are nonnegative, and summing first over $h_n$, then successively over the preceding coordinates, removes one normalized conditional at each step. No compatibility with an exchangeable population model is assumed. The model parameters, including any choice depending on the fixed sample size, stay fixed during this normalization sum.

## Copying-model conditionals

For the [Li–Stephens copying model](hmm.md), use $\mathcal H=\{0,1\}^{\ell}$ with $\ell\ge1$. A nonempty reference panel of size $K$ defines a conditional law of the target haplotype when the switch and mismatch probabilities lie in $[0,1]$. Its [uniform initial reference weights sum to one](init-sum.md), its [transition rows sum to one](trans-row-sum.md), and its [emissions sum to one over the target allele](emit-sum-bool.md) for each **fixed panel column**. Summing the finite hidden-path expression over all target haplotypes and then over the hidden states therefore gives one. The panel columns are conditioned on, not additional observations to sum over. The empty reference panel is not used to define $q_0$: the canonical zero-panel HMM has no normalized initial law.

## A two-sample order counterexample

For a one-site Boolean haplotype, take $q_0(0)=3/4$, $q_0(1)=1/4$, and the singleton-panel copying conditional with mismatch probability $\varepsilon=1/4$. Then

$$L(0,1)=\frac34\frac14=\frac3{16},\qquad L(1,0)=\frac14\frac14=\frac1{16}.$$

This uses an explicitly nonuniform first-haplotype law, allowed by the normalized-conditional hypotheses. Appendix A of Li and Stephens allows a first-haplotype law independent of the recombination parameter; its uniform law is an example, not a requirement of the abstract PAC construction.

In contrast, with a uniform first-haplotype law and constant symmetric mismatch probability, a two-sample copying law is $2^{-\ell}\varepsilon^d(1-\varepsilon)^{\ell-d}$, where $d$ is the Hamming distance between the haplotypes. This is symmetric. A two-sample counterexample must not be claimed under that additional uniform-seed restriction.

## Order dependence with a uniform first-haplotype law

There is also a direct example in the paper's Appendix A parameterization. Take $n=3$, two biallelic sites, $q_0(h)=1/4$, $\widetilde\theta=(1+1/2)^{-1}=2/3$, and scaled recombination distance $R=2\log2$ between the sites. For a panel of size $K=1,2$, the paper's formulas (A1)–(A3) give the canonical model's switch probability $r_K=1-e^{-R/K}$ and mismatch probability $\varepsilon_K=\widetilde\theta/[2(K+\widetilde\theta)]$. Thus $(r_1,r_2)=(3/4,1/2)$ and $(\varepsilon_1,\varepsilon_2)=(1/5,1/8)$.

With two references, the hidden-path sum gives $q_2(01\mid00,11)=(1-r_2)\varepsilon_2(1-\varepsilon_2)+r_2/4=23/128$ and $q_2(11\mid00,01)=\varepsilon_2/2=1/16$. Consequently

$$L(00,11,01)=\frac14\frac1{25}\frac{23}{128}=\frac{23}{12800},\qquad L(00,01,11)=\frac14\frac4{25}\frac1{16}=\frac1{400}.$$

The same sample multiset has different probabilities in these orders. Here $R$ is the paper's recombination parameter times marker distance, while $r_K$ is the switch probability supplied to the canonical HMM; they are not the same parameter. This example uses $\widehat\pi_A$, not Appendix B's empirical bias correction.

## Full symmetrization and sampled orders

Let $S_n$ act by permuting sample positions, including positions holding repeated haplotypes, and define

$$\overline L(h)=\frac1{n!}\sum_{\sigma\in S_n}L(h_{\sigma(1)},\ldots,h_{\sigma(n)}).$$

Every coordinate permutation is a bijection of $\mathcal H^n$, so each summand is normalized and $\sum_h\overline L(h)=1$. For any permutation $\tau$, composition with $\tau$ permutes the summands, proving $\overline L(h_\tau)=\overline L(h)$. Thus the full average is an exchangeable probability law for this fixed sample size. Permutations are of the positions: repeated haplotypes retain their permutation multiplicities.

For $m\ge1$ independent uniform permutations $\sigma_1,\ldots,\sigma_m$, the arithmetic average $\widehat L_m(h)=m^{-1}\sum_{j=1}^mL(h_{\sigma_j})$ satisfies $E[\widehat L_m(h)]=\overline L(h)$ by linearity of expectation. A finite realization is **not generally exchangeable**. Using the same fixed list of permutations for all inputs preserves total mass one, but does not generally restore exact symmetry. Li and Stephens use 20 random orders unless otherwise stated; this is a sampled approximation to the full average, not an assertion that 20 terms remove all order dependence. Averaging log likelihoods is a different operation and is not this normalized arithmetic symmetrization.

These results establish normalization and the stated order properties. They do not establish that the approximation is the true coalescent likelihood or supply uncertainty calibration for parameter estimates.

## Depends on

- [The Li–Stephens copying model](hmm.md)

## Proof depends on

- [Uniform initial reference weights sum to one](init-sum.md)
- [Li–Stephens transition rows sum to one](trans-row-sum.md)
- [Biallelic emissions sum to one for a fixed panel column](emit-sum-bool.md)

## Sources

- N. Li and M. Stephens, "Modeling linkage disequilibrium and identifying recombination hotspots using single-nucleotide polymorphism data", Genetics 165 (2003), 2213–2233, <https://doi.org/10.1093/genetics/165.4.2213>, equations (2)–(3), the order-dependence discussion on p.2216, and Appendix A, equations (A1)–(A3). The finite-sum normalization, permutation argument and explicit counterexamples are derived above. The first counterexample uses the stated nonuniform seed; the second uses the uniform-seed Appendix A formulas with the displayed parameters.
