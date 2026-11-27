# Bias from truncating or discarding negative heritability estimates

Suppose a heritability estimate is approximately normal around a true value $\psi_0\ge0$,

$$\hat\psi\approx\psi_0+\sigma_0X,\qquad X\sim N(0,1),$$

with $\sigma_0>0$ the asymptotic standard deviation (for GREML, of order $(n\tau^2)^{-1/2}$, where $n\tau^2$ grows with the sample size and the spread of the relatedness eigenvalues). Write $\Phi$ and $\varphi(x)=e^{-x^2/2}/\sqrt{2\pi}$ for the standard normal distribution function and density.

**Truncation at zero.** Replacing negative estimates by $0$, i.e. using $\max(\hat\psi,0)$, has bias

$$\mathbb E[\max(\psi_0+\sigma_0X,0)]-\psi_0=-\psi_0\,\Phi\!\left(-\frac{\psi_0}{\sigma_0}\right)+\sigma_0\,\varphi\!\left(\frac{\psi_0}{\sigma_0}\right).$$

For $\psi_0>0$ it is positive and at most $\dfrac{\sigma_0^3}{\sqrt{2\pi}\,\psi_0^2}\,e^{-\psi_0^2/(2\sigma_0^2)}$, hence negligible once $\sigma_0\ll\psi_0$. For $\psi_0=0$ it equals $\sigma_0/\sqrt{2\pi}$, of the same order as the standard error.

**Discarding negative estimates.** Averaging only the estimates that are nonnegative has bias

$$\mathbb E[\hat\psi\mid\hat\psi\ge0]-\psi_0=\frac{\sigma_0\,\varphi(\psi_0/\sigma_0)}{\Phi(\psi_0/\sigma_0)},$$

which equals the truncation bias plus $\psi_0\Phi(-\psi_0/\sigma_0)$, divided by $\Phi(\psi_0/\sigma_0)=\mathbb P(X\ge-\psi_0/\sigma_0)$. At $\psi_0=0$ it is $2\sigma_0/\sqrt{2\pi}$, twice the truncation bias; for $\psi_0>0$ it exceeds the truncation bias divided by $\Phi(\psi_0/\sigma_0)$ (the form stated in the source's text after its Eq. (5)), which is correct only at $\psi_0=0$.

## Expansion

- $\mathbb E[(\psi_0+\sigma_0X)\mathbf 1\{X>-\psi_0/\sigma_0\}]=\psi_0\Phi(\psi_0/\sigma_0)+\sigma_0\varphi(\psi_0/\sigma_0)$, since $\int_a^\infty x\varphi(x)\,dx=\varphi(a)$; subtracting $\psi_0$ and using $1-\Phi(x)=\Phi(-x)$ gives the formula.
- With $x=\psi_0/\sigma_0>0$, the Mills-ratio bounds $\varphi(x)(1/x-1/x^3)\le\Phi(-x)\le\varphi(x)/x$ give $0<\sigma_0\varphi(x)-\psi_0\Phi(-x)\le\psi_0\varphi(x)/x^3=\sigma_0^3\varphi(x)/\psi_0^2$.
- Conditioning on $\hat\psi\ge0$ divides the first display by $\Phi(\psi_0/\sigma_0)$: $\mathbb E[\hat\psi\mid\hat\psi\ge0]=\psi_0+\sigma_0\varphi(\psi_0/\sigma_0)/\Phi(\psi_0/\sigma_0)$. At $\psi_0=0$ the probability is $1/2$; at $\psi_0=\sigma_0$ the bias is about $0.288\,\sigma_0$.
- Truncation is warranted (and lowers mean squared error) only when the true heritability is known to be nonnegative; tests of $\psi_0=0$ are most affected, and silently discarded negative estimates leave no trace of the bias.

## Sources

- D. Steinsaltz, A. Dahl, K. W. Wachter, *On negative heritability and negative estimates of heritability*, Genetics 215 (2020), 343–357, <https://doi.org/10.1534/genetics.120.303161>, PMCID PMC7268991 (section Bias from rejecting negative heritability estimates, Equation 5).
