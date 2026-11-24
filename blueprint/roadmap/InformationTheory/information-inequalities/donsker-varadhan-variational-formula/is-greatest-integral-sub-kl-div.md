# Gibbs variational principle

For a probability measure $\nu$ and a bounded measurable function $f$,

$$\log \int e^{f} \, d\nu = \max \Bigl\{ \int f \, d\mu - \mathrm{KL}(\mu \,\|\, \nu) \;:\; \mu \text{ a probability measure}, \ \mathrm{KL}(\mu \,\|\, \nu) < \infty \Bigr\},$$

and the maximum is attained at the tilted (Gibbs) measure
$d\nu_f = e^{f} \, d\nu / \int e^{f} d\nu$, for which
$\mathrm{KL}(\nu_f \,\|\, \nu) = \int f \, d\nu_f - \log \int e^{f} d\nu$.

This is the dual of the Donsker–Varadhan formula: logarithmic moment generating functionals and
relative entropy are Legendre transforms of each other. In statistical mechanics it says that the
free energy is the minimum over states of energy minus entropy, attained at the Gibbs state.

## Sources

- S. R. S. Varadhan, "Large deviations", *Ann. Probab.* 36 (2008), 397–419, Section 2 (arXiv:0804.2330): $\log \int e^{V} d\alpha = \sup_\beta [\int V \, d\beta - H(\beta, \alpha)]$.
- P. Alquier, User-friendly introduction to PAC-Bayes bounds, *Foundations and Trends in Machine Learning* 17 (2024), arXiv:2110.11216, Lemma 2.2 (stated there as Donsker and Varadhan's variational formula, with the maximiser given by the Gibbs measure (2.1)).
