# Global attractor of the Yoccoz–Birkeland integral equation

**Setting.** The **Yoccoz–Birkeland model** describes the number $N(t)$ of sexually mature females (time in years) of a species with maturation age $A_0$, maximal age $A_1$, density-dependent fertility $m(N)$ (female offspring per female per year in good conditions), seasonal reproduction fraction $\rho(t) \in [0,1]$ (typically 1-periodic) and the linear survival function $\varsigma(a) = 1 - a/A_1$ on $[0,A_1]$ (the source's choice (2.2), on which $N_{max}$ and $L$ below depend):

$$N(t) = \int_{A_0}^{A_1} N(t-a)\,m\big(N(t-a)\big)\,\rho(t-a)\,\varsigma(a)\,da.$$

Given $N$ on $[t_0 - A_1, t_0]$, this determines $N$ for all later times, defining a semiflow $T^s$ on histories.

**Theorem (Theorem 2.1, from Arlot).** Assume $N \mapsto Nm(N)$ is uniformly continuous on $[0,\infty)$ and
1. $m_0/2 \le m(N) \le m_0$ for $N \le 1$ and $\min\{1/2, N^{-\gamma}\}m_0 \le m(N) \le m_0N^{-\gamma}$ for $N \ge 1$, with $\gamma \ge 1$;
2. $0 \le \rho \le 1$ and $\rho = 1$ on an interval of length $1 - \rho_w$ each year, with $0 < \rho_w < 1$ (a positive winter length);
3. $A_1 \ge \max\{2A_0, A_0 + 1\}$ and $c_0m_0 > 2$, where $c_0 = \int_{A_0+\rho_w}^{A_0+1}\varsigma(a)\,da$.

Let $N_{max} = m_0\frac{A_1}{2}\big(1 - \frac{A_0}{A_1}\big)$, $L = m_0\big(3 - \frac{A_0}{A_1}\big)$ and $\mathcal K$ the set of histories with $\frac{c_0m_0}{2}N_{max}^{1-\gamma} \le N \le N_{max}$ on $[-A_1, 0]$ that are $L$-Lipschitz. Then $\mathcal K$ is compact and forward invariant, every non-trivial history enters $\mathcal K$ in finite time, and $\Lambda = \bigcap_{n\ge0}T^n(\mathcal K)$ is a non-empty compact invariant global attractor.

**Coupling with prices (Theorems 4.10–4.11).** If, at birth, a price-dependent fraction $R(P) \in [0,1]$ of the cattle population is kept as reproducing females (so the integrand of the population equation is multiplied by $R(P(t-a))$) and the rest, entering the slaughter supply $S(t)$ with weight $2 - R(P(t-a))$, is sent to butchery at ages in $[\Omega_0, \Omega_1]$, and the commodity price obeys $P'/P = \lambda\,\frac{D(P) - S}{D(P) + S}$ with demand $D$ and slaughter supply $S$, then under $m_0R_0c_0 > 2$ (with $R_0$ a lower bound for $R$), $D(0) > S_{max}$ and $S_{min} > 0$ the coupled system again has a global attractor (for its time-one map) and admits a non-trivial 1-periodic solution, while simulations show chaotic price cycles.

## Expansion

The model was proposed for the Svalbard vole *Microtus epiroticus*, whose high average fertility coexists with large, near-extinction fluctuations without significant predation: a shortage of good breeding sites makes fertility decrease with density ($m(N) \sim N^{-\gamma}$ for large $N$), and a short summer makes early-summer births mature within the same season. The upper bound $N_{max}$ comes from $Nm(N) \le m_0$ for $\gamma \ge 1$, which caps births, and the lower bound from a full good season ($\rho = 1$ on an interval) recruiting at least $c_0m_0/2$ times the minimal parent stock; condition $c_0m_0 > 2$ makes the population persist uniformly. The integral form makes histories Lipschitz after one generation, which gives the compactness needed for an attractor; the dynamics on $\Lambda$ can be irregular, which is how the model reproduces erratic abundance cycles.

## Sources

- Sylvain Arlot, Stefano Marmi and Duccio Papini, "Coupling the Yoccoz–Birkeland population model with price dynamics: chaotic livestock commodities market cycles", arXiv:1803.05404 (2018), Section 2 (model with the choices (2.2)–(2.3), and Theorem 2.1) and Section 4 (Propositions 4.2, 4.4, Theorems 4.10–4.11), <https://doi.org/10.48550/arXiv.1803.05404>. Published version: Nonlinearity, Volume 32 (2019), Number 7, 2564-2592, <https://doi.org/10.1088/1361-6544/ab0eb7>.
