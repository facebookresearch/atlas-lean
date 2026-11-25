# Security levels, policies and low equivalence

Security levels form a lattice $(\mathcal{L}, \sqsubseteq)$, in the simplest case the two-point lattice $L \sqsubseteq H$ of public and secret data. A *security policy* $\Gamma$ assigns a level to each program variable. For an observer at level $\ell$, two stores $\sigma_1$ and $\sigma_2$ are *low equivalent*, written $\sigma_1 =_\ell \sigma_2$, if $\sigma_1(x) = \sigma_2(x)$ for every variable $x$ with $\Gamma(x) \sqsubseteq \ell$. Low equivalence is an equivalence relation on stores.

In the lattice model a flow of information from $x$ to $y$ is permitted when $\Gamma(x) \sqsubseteq \Gamma(y)$, and least upper bounds give the level of information
combined from several variables. Only the partial order is needed to define low equivalence.

## Sources

- D. Volpano, C. Irvine and G. Smith, "A sound type system for secure flow analysis", *Journal of Computer Security* 4(2–3):167–187, 1996, copy at <https://people.cs.ksu.edu/~tamtoft/890/10Fall/Vol+Smi+Irv:JCS-1996.pdf>: Section 2, "The lattice model of information flow" (security classes, permitted flows, least upper bounds).
- A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE Journal on Selected Areas in Communications* 21(1):5–19, 2003, <https://www.cs.cornell.edu/andru/papers/jsac/sm-jsac03.pdf>: Section II-G, "Noninterference" (low and high variables and the low-equivalence relation $=_L$ on states).
