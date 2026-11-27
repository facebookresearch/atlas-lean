# Rare-mutation LD under strong selection or recombination and in quasi-linkage equilibrium

In the rare-mutation setting of the [frequency-resolved LD statistics](frequency-weighted-ld-sigma-d-k-rare-mutation-scaling.md), with scaled parameters $\rho=2NRf_0$, $\gamma_i=2Ns_if_0$ and $\gamma_{AB}=\gamma_A+\gamma_B+\gamma_\epsilon+\rho$:

1. **Strong selection or recombination.** If at least one of $\gamma_A,\gamma_B,\rho$ is large compared with $1$, the first two scaling functions are, to leading order,

$$\Sigma_d^1\approx0,\qquad \Sigma_d^2\approx\frac{2+\gamma_A+\gamma_B+\rho}{(\gamma_A+\gamma_B+\gamma_\epsilon+\rho)^2},$$

so that $\sigma_d^2(f_0)\approx f_0\,\Sigma_d^2$. For neutral loci this reduces to $(2+\rho)/\rho^2\sim1/\rho$, that is $\sigma_d^2(f_0)\approx1/(2NR)$ when $\rho\gg1$. For the neutral one-parameter curve $\Sigma_d^k(\rho)$ the paper gives an exact integral in terms of the exponential integral $E_1$, with asymptotics $\Sigma_d^2\sim1/\rho$ as $\rho\to\infty$ and $\Sigma_d^2\sim\log(1/\rho)$ as $\rho\to0$, and a slow $1/\log(1/\rho)$ correction to the latter.

2. **Signed LD.** Frequency-matched neutral mutations (with $f_0=1/(2Ns)$) show coupling excess $\sigma_d^1(f_0)>0$ at small $\rho$, produced by old nested mutations. Strongly deleterious additive mutations have $\sigma_d^1\approx0$, and additive costs alone do not make $\sigma_d^1$ negative.

3. **Quasi-linkage equilibrium.** For neutral mutations with $\rho\gg1$ and $f_0\ll1$, but $\rho f_0$ not necessarily small, the double-mutant frequency equilibrates on the fast time scale $1/R$ given the single-mutant frequencies, to the gamma law

$$p(f_{AB}\mid f_{Ab},f_{aB})\propto f_{AB}^{\,2NRf_{Ab}f_{aB}-1}\,e^{-2NRf_{AB}},$$

with mean $f_{Ab}f_{aB}$. Averaging over the weighted single-locus spectra gives

$$\sigma_d^1(f_0)=0,\qquad \sigma_d^2(f_0)=\frac1{2NR},\qquad \sigma_d^4(f_0)=\frac{6+6NRf_0^2}{(2NR)^3}.$$

The first two moments agree with the clonal-recombinant regime $f_0^{-1}\ll NR\ll f_0^{-2}$, and the fourth moment separates them. The ratio $\eta(f_0)=\sigma_d^4(f_0)/[3\sigma_d^2(f_0)]$, where the superscripts index the moments $k=4$ and $k=2$ rather than powers, decays like $(NR)^{-2}$ in the clonal-recombinant regime and like $f_0^2/(NR)$ in quasi-linkage equilibrium.

## Depends on

- [Frequency-resolved linkage disequilibrium $\sigma_d^k(f_0)$ and its rare-mutation scaling collapse](frequency-weighted-ld-sigma-d-k-rare-mutation-scaling.md)

## Proof depends on

- [Mean of the gamma law](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md)
- [Variance of the gamma law](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md)
- [Gamma integrals](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-pow-mul-exp-neg-mul-gamma-measu.md)

## Related topics

- [Stationary standardized linkage disequilibrium $\sigma_d^2$](sigma-dsq.md)

## Expansion

Item 1 comes from a separation of time scales in the characteristic equation, treating the $\psi^2$ (drift) term as a perturbation. It matches the $\rho=0$ and neutral limits. Item 3 can be checked directly from gamma moments. With shape $a=2NRxy$ and rate $\lambda=2NR$, where $x=f_{Ab}$ and $y=f_{aB}$, $D\approx f_{AB}-xy$ is the centred variable. Its variance is $a/\lambda^2=xy/(2NR)$, and its fourth central moment is $3a(a+2)/\lambda^4=3x^2y^2/(2NR)^2+6xy/(2NR)^3$. Under the neutral weighted spectrum $p(f\mid f_0)\propto e^{-f/f_0}/f$ one has $\langle f^2e^{-f/f_0}\rangle/\langle fe^{-f/f_0}\rangle=f_0$. So $\langle x^2y^2\,w\rangle/\langle xy\,w\rangle=f_0^2$ for the product weight $w$, which gives $\sigma_d^2=1/(2NR)$ and $\sigma_d^4=3f_0^2/(2NR)^2+6/(2NR)^3$, the stated formula. The denominator $f_A(1-f_A)f_B(1-f_B)\approx xy$ to leading order.

## Sources

- B. H. Good, "Linkage disequilibrium between rare mutations", Genetics 220(4) (2022), iyac004, <https://doi.org/10.1093/genetics/iyac004>, PMCID PMC8982034. Equations (63)-(65) (neutral exact integral and its asymptotics), (66) (strong selection or recombination), (67)-(70) (quasi-linkage equilibrium), and the discussion of Fig. 5 (signed LD of deleterious vs frequency-matched neutral mutations).
