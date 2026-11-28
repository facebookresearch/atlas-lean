# Intermitotic-time distribution of an age-structured population and inversion for the division rate

**Model.** Proliferating cells of age $a$ (time since birth) have density $p(t,a)$, divide at age-dependent rate $\beta(a)\ge0$ and die at rate $\mu\ge0$; a fraction $f\in[0,1]$ of daughters becomes quiescent ($Q$):

$$
\partial_tp+\partial_ap+\bigl(\beta(a)+\mu\bigr)p=0,\qquad p(t,0)=2(1-f)\int_0^\infty\beta(a)p(t,a)\,da,\qquad Q'(t)=2f\int_0^\infty\beta(a)p(t,a)\,da-\mu Q .
$$

The probability that a cell has not divided by age $a$ is $e^{-\int_0^a\beta}$, so one assumes $\int_0^\infty\beta=\infty$ (every cell eventually divides). At exponential equilibrium with Malthus parameter $\lambda$, the age profile is $\hat p(a)\propto e^{-\int_0^a(\beta+\mu+\lambda)}$. In a live-cell experiment, cells present during a labeling window of length $t_0$ (ages truncated to $[0,t_0]$) are tracked until time $T$, and the histogram of their **intermitotic times** (ages at division) is

$$
I_T(a)=C_T^{-1}\int_0^T\beta(a)\,\bar p(t,a)\,dt ,
$$

with $\bar p$ the transported truncated equilibrium profile and $C_T$ a normalization.

**Claim (Claim 1) and theorem (appendix).** Assume $\int_0^\infty\beta=\infty$ and $\beta(a)=0$ for $a\le t_0$ (no cell divides faster than $t_0$), and the initial age distribution vanishes beyond $t_0$. Then

$$
\int_0^\infty\bigl|I_T(a)-I_\infty(a)\bigr|\,da\longrightarrow0\quad(T\to\infty),\qquad I_\infty(a)=\frac{\beta(a)e^{-\int_0^a(\beta+\mu)}}{\int_0^\infty\beta(s)e^{-\int_0^s(\beta+\mu)}\,ds}.
$$

If in addition $\beta(a)e^{-\int_0^a\beta}\to0$ (e.g. $\beta$ bounded or monotone), the convergence is uniform in $a$.

**Inversion.** Without death ($\mu=0$), $I_\infty(a)=\beta(a)e^{-\int_0^a\beta}$ is the density of the division age, and the division rate is its hazard function:

$$
\beta(a)=\frac{I_\infty(a)}{\int_a^\infty I_\infty(s)\,ds}.
$$

Fitting a positively skewed parametric density to measured intermitotic times (e.g. exponentially modified Gaussian, giving $\beta(a)=\beta_0\,\mathrm{Erfc}((m-a)/\sigma)$ shapes) therefore determines $\beta$; with death, $\mu$ and $\beta$ are fitted jointly to $I_\infty$ and the observed growth rate.

## Expansion

Along characteristics $\bar p(t,a)=\rho e^{-\int_0^a(\beta+\mu+\lambda)}e^{\lambda t}$ on $t\le a\le t+t_0$, so integrating $\beta\bar p$ over $t\in[0,T]$ gives, for each age $a$, a factor $\int_{\max(0,a-t_0)}^{\min(a,T)}e^{\lambda t}dt$ times $\beta(a)e^{-\int_0^a(\beta+\mu+\lambda)}$. Because $\beta=0$ on $[0,t_0]$, only ages $a>t_0$ contribute, where for $T\ge a$ the factor equals $e^{\lambda a}(1-e^{-\lambda t_0})/\lambda$, exactly cancelling the $e^{-\lambda a}$ in the profile; hence $I_T\to I_\infty$, with the tail $a>T$ vanishing in $L^1$ because $\int_0^\infty\beta e^{-\int\beta}=1$. The inversion follows from $\frac{d}{da}e^{-\int_0^a\beta}=-I_\infty(a)$, so $\int_a^\infty I_\infty=e^{-\int_0^a\beta}$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Sources

- P. Gabriel, S. P. Garbett, V. Quaranta, D. R. Tyson and G. F. Webb, "The contribution of age structure to cell population responses to targeted therapeutics", arXiv:1112.1590 (2011), Section 2 (age-structured model with quiescence), Section 3 (Eqs. for $I_T$, $I_\infty$, Claim 1 and remark), Section 4 (inversion formula) and appendix on convergence of the IMT distribution, <https://doi.org/10.48550/arXiv.1112.1590>.
