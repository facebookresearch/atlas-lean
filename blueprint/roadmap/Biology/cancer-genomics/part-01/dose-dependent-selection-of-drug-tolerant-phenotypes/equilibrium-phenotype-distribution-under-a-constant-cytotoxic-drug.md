# Equilibrium phenotype distribution under a constant cytotoxic drug

Let $x\in\mathbb R$ be the rescaled expression level of a gene that controls both drug resistance and proliferative potential, normalised so that $x=0$ is the most proliferative state without drug and $x=1$ is the most drug-resistant state. Let $n(x,t)\ge 0$ be the density of cancer cells with total number $\rho(t)=\int_{\mathbb R}n\,dx$, mean phenotype $\mu(t)=\rho^{-1}\int xn\,dx$ and variance $\sigma^2(t)=\rho^{-1}\int x^2n\,dx-\mu^2$. Under continuous infusion of a cytotoxic drug at constant concentration $C>0$ the density solves

$$\partial_t n=\beta\,\partial_{xx}n+\Big(\gamma-\eta x^2-d\,\rho(t)-C(x-1)^2\Big)n,\qquad x\in\mathbb R,\ t>0,$$

where $\beta>0$ is the rate of random epimutations, $\gamma>0$ the maximal fitness, $\eta>0$ the selection gradient without drug, $d>0$ the death rate from competition, and $C(x-1)^2$ the drug-induced death rate. Assume $n$ and all its $x$-derivatives vanish as $|x|\to\infty$, and $n(\cdot,0)\in L^1\cap L^\infty(\mathbb R)$ with $n(\cdot,0)>0$ a.e. on a compact set. Define

$$\gamma_C=\gamma-\frac{\eta C}{\eta+C},\qquad \eta_C=\eta+C,\qquad \bar x_C=\frac{C}{\eta+C}.$$

1. If $\gamma_C\le(\beta\eta_C)^{1/2}$, then $\rho(t)\to 0$ as $t\to\infty$ (extinction).
2. If $\gamma_C>(\beta\eta_C)^{1/2}$, then $\rho(t)\to\bar\rho_C=\big(\gamma_C-(\beta\eta_C)^{1/2}\big)/d$, the unique nontrivial non-negative equilibrium is the Gaussian

    $$\bar n_C(x)=\bar\rho_C\,\frac{(\eta_C/\beta)^{1/4}}{(2\pi)^{1/2}}\exp\!\Big(-\tfrac12\Big(\frac{\eta_C}{\beta}\Big)^{1/2}(x-\bar x_C)^2\Big),$$

    and $\mu(t)\to\bar x_C$, $\sigma^2(t)\to(\beta/\eta_C)^{1/2}$.

Hence the selected phenotype $\bar x_C$ increases from $0$ to $1$ as the dose $C$ increases, so intermediate doses select intermediate resistance; the equilibrium heterogeneity $(\beta/\eta_C)^{1/2}$ decreases with $C$; and $\bar\rho_C$ decreases with $C$ because $d\gamma_C/dC=-\eta^2/(\eta+C)^2<0$ and $\eta_C$ increases. Setting $C=0$ gives the drug-free case $\bar x_0=0$, $\bar\rho_0=(\gamma-(\beta\eta)^{1/2})/d$, and the extinction condition $\beta\eta\ge\gamma^2$.

## Expansion

Completing the square, $\gamma-\eta x^2-C(x-1)^2=\gamma_C-\eta_C(x-\bar x_C)^2$, so after translating $x\mapsto x-\bar x_C$ the problem is the drug-free model with parameters $(\gamma_C,\eta_C)$. For an equilibrium, $\beta\bar n''+(\gamma_C-\eta_C x^2-d\bar\rho)\bar n=0$; the substitution $z=(4\eta_C/\beta)^{1/4}x$ turns it into Weber's equation $Y''-(z^2/4+a)Y=0$ with $a=(d\bar\rho-\gamma_C)/(2(\beta\eta_C)^{1/2})$. Bounded solutions exist only for $a=-m-\tfrac12$, $m\in\mathbb N_0$, and are Hermite functions; only $m=0$ is non-negative, which forces $d\bar\rho=\gamma_C-(\beta\eta_C)^{1/2}$ and the Gaussian profile. The long-time limit of $\rho$ follows from writing $\rho(t)=g(t)\rho(0)/\big(g(0)+d\rho(0)\int_0^tg\big)$, where $g$ grows like $e^{(\gamma_C-(\beta\eta_C)^{1/2})t}$, so $\rho$ tends to $\bar\rho_C$ when the exponent is positive and to $0$ otherwise. The authors prove the drug-free case and state that the drug case follows by the same argument after the translation.

## Sources

- T. Lorenzi, R. H. Chisholm, J. Clairambault, "Tracking the evolution of cancer cell populations through the mathematical lens of phenotype-structured equations", Biology Direct (2016), Methods Eqs. (1)–(7); Results, Theorem 1 (Eqs. (9)–(12)) and Theorem 2 (Eqs. (13)–(18)); Appendix 1 (Lemmas 1–2, Eqs. (19)–(23)) and Appendix 2 (Eq. (25)), <https://doi.org/10.1186/s13062-016-0143-4>, PMCID PMC4994266.
