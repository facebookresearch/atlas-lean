# Controlled and uncontrolled parasite infection in a dividing cell population with reinfection

**Setting.** Use the cell-population model with parasite load dynamics $(g,\sigma,p,\pi)$, division rate $b$ with symmetric sharing law $\Theta$, death rate $d$, reservoir reinfection rate $\lambda(x)$ with amounts $\mathcal I$, and lysis reinfection rate $r(\cdot)$ with amounts $\mathcal P$ (see the depended-on article), with $b>d$ so that the cell population survives with positive probability. Let $N_t$ be the number of living cells and $V_t$ the set of living cells. Define

$$\rho(x)=\mathbb E[\mathcal I]\,\lambda(x)+\mathbb E[\mathcal P]\,r(x)+g(x)-bx,\qquad x\ge0 .$$

**Proposition (controlled versus uncontrolled infection).** Start from one cell with no parasites, $Z_0=\delta_0$.
1. If $g(x)+\mathbb E[\mathcal I]\lambda(x)\le\tilde g\,x$ for large $x$ with $\tilde g<b$, there is $C<\infty$ such that for all $K,t\ge0$,

$$\mathbb E_{\delta_0}\Big[\mathbf 1_{\{N_t\ge1\}}\frac{\#\{u\in V_t:X^u_t\ge K\}}{N_t}\Big]\le\frac{C}{\sqrt K}.$$

The infection is controlled: at any fixed time the fraction of heavily infected cells is small.
2. If $g(x)+\mathbb E[\mathcal I]\lambda(x)\ge\tilde g\,x$ for all $x>0$ with $\tilde g>b$, then for every $K\ge0$,

$$\mathbf 1_{\{N_t\ge1\}}\frac{\#\{u\in V_t:\sup_{s\le t}X^u_s\le K\}}{N_t}\xrightarrow[t\to\infty]{}0\quad\text{in probability};$$

in the long run almost every lineage has carried more than $K$ parasites at some time.

**Proposition (clearing the infection without a reservoir).** Assume $\lambda\equiv0$, $g$ concave, and $\rho(x)\le-(\alpha x\wedge\eta)$ for all $x\ge0$ and some $\alpha,\eta>0$. Then for every $\varepsilon>0$ and $Z_0=\delta_{x_0}$ with $x_0<\infty$,

$$\mathbf 1_{\{N_t\ge1\}}\frac{\#\{u\in V_t:X^u_t>\varepsilon\}}{N_t}\xrightarrow[t\to\infty]{}0\quad\text{in probability}.$$

Parasite growth $g$ and reservoir reinfection $\mathbb E[\mathcal I]\lambda$ enter the criteria only through their sum, so reinfection from outside the population can turn a controlled infection into an uncontrolled one.

## Proof sketch

Each statement is first proved for the typical-cell process $Y$ of the many-to-one formula and then transferred to the population: the formula gives $e^{-(b-d)t}\mathbb E\big[\sum_{u}\mathbf 1\{X^u_t\in A\}\big]=\mathbb P(Y_t\in A)$, and $N_te^{-(b-d)t}$ converges to an exponential variable on the survival event (and its law is explicitly geometric for a linear birth–death process), which controls the random denominator. For (1), Itô's formula with jumps applied to $e^{(b-\tilde g)t}Y_t$, a comparison with a process whose lysis rate is frozen at a level $\bar y$, and Grönwall's lemma give $\sup_t\mathbb E[Y_t]\le\bar y$; Markov's inequality then gives $\mathbb P(Y_t\ge K)\le\bar y/K$, and splitting on $\{N_te^{-(b-d)t}\le K^{-1/2}\}$ yields the $C/\sqrt K$ bound. For (2), $\mathbb E[e^{(b-\tilde g)t}Y_t]$ is non-decreasing, so $Y$ exceeds any level with positive probability within a bounded time, and a renewal argument makes $\mathbb P(\sup_{s\le t}Y_s\le K)\to0$. For the clearing result, concavity and Jensen's inequality give a differential inequality forcing $\mathbb E[Y_t]\to0$.

## Depends on

- [Many-to-one formula for parasite loads in a dividing cell population with reinfection](many-to-one-formula-for-parasite-loads-with-reinfection.md)

## Sources

- Charline Smadi, "Parasite infection in a cell population with deaths and reinfections", *MathematicS In Action* 12 (2023), 23–47, <https://doi.org/10.5802/msia.30>. Preprint version: arXiv:2111.05084 (2021), Section 2.1, Proposition 2.1 (points 1 and 2); Section 2.2, Proposition 2.2 (point 1); Section 3, <https://doi.org/10.48550/arXiv.2111.05084>.
