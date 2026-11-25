# Donsker–Varadhan variational formula

For probability measures $\mu$ and $\nu$ on a measurable space,

$$\mathrm{KL}(\mu \,\|\, \nu) = \sup_f \Bigl( \int f \, d\mu - \log \int e^{f} \, d\nu \Bigr)^{+},$$

the supremum being over bounded measurable $f$, with $\mathrm{KL}(\mu \,\|\, \nu) = \infty$ unless
$\mu \ll \nu$ with integrable log-likelihood ratio. (The positive part is harmless: $f = 0$
gives the value $0$.)

The inequality $\ge$ is the [Donsker–Varadhan inequality](of-real-integral-sub-log-integral-exp-le.md).
For $\le$: if $\mu \not\ll \nu$, the functions $t \mathbf{1}_A$ with $\nu(A) = 0 < \mu(A)$ make the
supremum infinite; if $\mu \ll \nu$ with density $\rho$, the clamped log-densities
$f_k = \max(-k, \min(\log \rho, k))$ (with $f_k = -k$ where $\rho = 0$) satisfy, by $\log z \le z - 1$,
$\int f_k \, d\mu - \log \int e^{f_k} d\nu \ge \int (\rho f_k - e^{f_k} + 1) \, d\nu$, and Fatou's lemma
gives $\liminf_k$ of the right side $\ge \int (\rho \log \rho - \rho + 1) \, d\nu = \mathrm{KL}(\mu \,\|\, \nu)$.

Relative entropy is thus the Legendre transform of the functional $f \mapsto \log \int e^f d\nu$;
this is the form in which it enters the upper bound of Sanov's theorem, and its inequality half
is the change-of-measure step of PAC-Bayes bounds.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 3, Lemma 1.2 in the notes' numbering (https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf).
