# Security levels, policies and low equivalence

Security levels form a lattice $(\mathcal{L}, \sqsubseteq)$, in the simplest case the two-point lattice $L \sqsubseteq H$ of public and secret data. A *security policy* $\Gamma$ assigns a level to each program variable. For an observer at level $\ell$, two stores $\sigma_1$ and $\sigma_2$ are *low equivalent*, written $\sigma_1 =_\ell \sigma_2$, if $\sigma_1(x) = \sigma_2(x)$ for every variable $x$ with $\Gamma(x) \sqsubseteq \ell$. Low equivalence is an equivalence relation on stores.

## Sources

- A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE Journal on Selected Areas in Communications* 21(1):5–19, 2003
- D. E. Denning, "A lattice model of secure information flow", *Communications of the ACM* 19(5):236–243, 1976
