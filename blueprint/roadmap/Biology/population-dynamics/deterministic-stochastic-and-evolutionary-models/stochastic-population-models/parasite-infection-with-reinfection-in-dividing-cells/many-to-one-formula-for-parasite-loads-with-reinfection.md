# Many-to-one formula for parasite loads in a dividing cell population with reinfection

**Model.** Cells carry a nonnegative quantity of parasites. Between events, the load of a cell follows

$$d\mathfrak X_t=g(\mathfrak X_t)\,dt+\sqrt{2\sigma^2(\mathfrak X_t)}\,dB_t+\int_0^{p(\mathfrak X_{t-})}\!\!\int_{\mathbb R_+}z\,\widetilde Q(dt,dx,dz),$$

with $\widetilde Q$ a compensated Poisson measure of intensity $dt\,dx\,\pi(dz)$; the states $0$ and $+\infty$ are absorbing. In addition:
- each cell divides at constant rate $b$ into two cells with loads $\Theta x$ and $(1-\Theta)x$, where $\Theta\in(0,1)$ has a symmetric law $\kappa$ with $\mathbb E[\ln(1/\Theta)]<\infty$;
- each cell dies at constant rate $d$;
- a cell with load $x$ is reinfected from an external reservoir at rate $\lambda(x)$ by an amount with law $\mathfrak I$;
- a cell is reinfected by parasites released at cell lysis at rate $r(\bar m_t)$ by an amount with law $\mathfrak P$, where $\bar m_t=e^{-(b-d)t}\,\mathbb E[\langle Z_t,\mathrm{Id}\rangle]$ is the mean parasite quantity per expected cell.

Assume $p$ locally Lipschitz, non-decreasing with $p(0)=0$; $g$ continuous with $g(0)=0$ and a local $x(1-\ln x)$-type modulus of continuity; $\sigma$ locally $\tfrac12$-Hölder with $\sigma(0)=0$; $\int(z\wedge z^2)\pi(dz)<\infty$; $\lambda,r$ continuous, $r$ non-decreasing and bounded with $r(0)=0$; and $\mathfrak I,\mathfrak P$ with finite means. Then the population, encoded as the point measure $Z_t=\sum_{u\in V_t}\delta_{X^u_t}$ over the set $V_t$ of living cells, exists and is strongly unique.

**Proposition (many-to-one formula).** For $x_0\ge0$, $t\ge0$ and every bounded measurable $F$ on paths $[0,t]\to[0,\infty]$,

$$\mathbb E_{\delta_{x_0}}\Big[\sum_{u\in V_t}F\big(X^u_s,\,s\le t\big)\Big]=e^{(b-d)t}\,\mathbb E_{x_0}\big[F(Y_s,\,s\le t)\big],$$

where $X^u_s$ is the load of the ancestor at time $s$ of cell $u$, and the auxiliary "typical cell" process $Y$ is the unique nonnegative strong solution of

$$\begin{aligned}Y_t={}&x_0+\int_0^t g(Y_s)\,ds+\int_0^t\sqrt{2\sigma^2(Y_s)}\,dB_s+\int_0^t\!\!\int_0^{p(Y_{s-})}\!\!\int z\,\widetilde Q(ds,dx,dz)+\int_0^t\!\!\int_0^{2b}\!\!\int_0^1(\theta-1)Y_{s-}\,N(ds,dx,d\theta)\\&+\int_0^t\!\!\int_0^{r(\mathbb E_{x_0}[Y_s])}\!\!\int \mathfrak p\,N_1(ds,dx,d\mathfrak p)+\int_0^t\!\!\int_0^{\lambda(Y_{s-})}\!\!\int\mathfrak i\,N_2(ds,dx,d\mathfrak i),\end{aligned}$$

with independent Poisson measures $N,N_1,N_2$ of intensities $ds\,dx\,\kappa(d\theta)$, $ds\,dx\,\mathfrak P(d\mathfrak p)$, $ds\,dx\,\mathfrak I(d\mathfrak i)$. The cell death rate $d$ does not enter $Y$, and division acts on $Y$ at the size-biased rate $2b$.

## Proof sketch

The proof adapts the many-to-one formula for structured branching processes with a trait-dependent flow between divisions. Since the division rate does not depend on the load, the expected number of cells is $e^{(b-d)t}$, and following a uniformly chosen lineage backwards sees divisions at twice the individual rate (two daughters per division) with load multiplied by $\Theta$. Death acts uniformly on all cells, so it cancels in the generator identity for the normalised first-moment semigroup and only contributes the factor $e^{(b-d)t}$. Reinfection events are additional positive jumps along the lineage. Because the lysis reinfection rate depends on $\mathbb E[Y_s]$, $Y$ is time-inhomogeneous and not Markov, but it is still well defined pathwise; its existence uses the general theory of nonnegative SDEs with jumps.

## Sources

- Charline Smadi, "Parasite infection in a cell population with deaths and reinfections", *MathematicS In Action* 12 (2023), 23–47, <https://doi.org/10.5802/msia.30>. Preprint version: arXiv:2111.05084 (2021), Section 1, Assumption EU, Propositions 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2111.05084>.
