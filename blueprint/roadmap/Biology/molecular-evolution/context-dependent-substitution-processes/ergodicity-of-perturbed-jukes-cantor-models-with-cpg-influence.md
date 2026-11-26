# Ergodicity of perturbed Jukes–Cantor models with CpG influence

**Model.** A DNA sequence indexed by $\mathbb{Z}$ evolves in continuous time as follows: every nucleotide $x$ mutates to each $y\ne x$ at rate $1+\varepsilon(x,y)$ with $\varepsilon(x,y)\ge0$ (a perturbed Jukes–Cantor model), and in addition every dinucleotide CpG mutates to CpA and to TpG, each at rate $\tau\ge0$ (CpG hypermutability, a neighbour-dependent rule). Let $|\varepsilon|=\sum_{x\ne y}\varepsilon(x,y)$. Put

$$\varepsilon_{\mathrm{sens}}(\tau)=\frac{64}{3(40+10\tau+\tau^2)},$$

and let $\varepsilon_{\mathrm{ins}}$ be the unique positive root of $3\varepsilon(64+12\varepsilon+\varepsilon^2)=64$.

**Theorem.** If $|\varepsilon|<\max\{\varepsilon_{\mathrm{ins}},\varepsilon_{\mathrm{sens}}(\tau)\}$, the process is ergodic, every finite marginal converges exponentially fast to that of the unique stationary distribution, and correlations of the stationary distribution decay exponentially in the distance between sites.

For example $\varepsilon_{\mathrm{sens}}(0)=8/15$, $\varepsilon_{\mathrm{sens}}(2)=1/3$, $\varepsilon_{\mathrm{sens}}(10)=4/45$, and $\varepsilon_{\mathrm{sens}}(\tau)\to0$ as $\tau\to\infty$; the insensitive bound gives ergodicity for every $\tau$ as soon as $|\varepsilon|\le3/10$.

## Depends on

- [Coupling times with ambiguities](coupling-times-with-ambiguities.md)

## Expansion

Two coupling mechanisms are built. A *sensitive* mechanism, based on coupling events that take the CpG rules into account (rate parameters $r_0=r_1=r_4=4$, $r_2=r_5=\tau$), has growth parameter is at most $\tfrac{3}{64}|\varepsilon|(40+10\tau+\tau^2)$. An *insensitive* mechanism (rate parameters $r_0=4$, $r_1=r_4=2$, with $r_2,r_5$ sums of perturbations) has growth parameter at most $\tfrac{3}{64}|\varepsilon|(64+12|\varepsilon|+|\varepsilon|^2)$. Both have width bounded by $(2,2)$ and exponentially integrable coupling time, so whenever either growth parameter is below $1$ the general theorems on subcritical coupling times with ambiguities give ergodicity, exponential convergence and exponential decay of correlations.

## Sources

- J. Bérard, D. Piau, "Coupling times with ambiguities for particle systems and applications to context-dependent DNA substitution models", arXiv:0712.0072 (2007), Theorem 5, Propositions 5.15 and 5.17, Section "Example: perturbed Jukes-Cantor model with CpG influence" and Theorem 6, <https://doi.org/10.48550/arXiv.0712.0072>.
