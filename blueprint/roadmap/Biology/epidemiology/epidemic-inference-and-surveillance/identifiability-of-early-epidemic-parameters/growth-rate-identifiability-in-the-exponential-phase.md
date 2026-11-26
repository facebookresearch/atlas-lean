# Growth-rate identifiability in the exponential phase

Consider an SIR-type model in which confirmed cases are a fraction of infections. Let $N$ be the population size, $\beta > 0$ the transmission rate (per contact pair), $\rho > 0$ the diagnosis (case-reporting) rate and $\mu > 0$ the recovery rate, with

$$S' = -\beta I S, \qquad I' = \beta I S - (\rho + \mu) I, \qquad R' = \rho I - d R,$$

and suppose the observed newly confirmed cases at time $t$ have mean $\rho I(t)$. During the initial phase $S(t) \approx S(0) \approx N$, so to first order

$$I(t) = I_0 \, e^{r t}, \qquad r = \beta N - \rho - \mu, \qquad \mathbb{E}[\text{new cases at } t] = \rho I_0 \, e^{r t} .$$

**Proposition (linearized nonidentifiability).** In the linear regime the mean case curve depends on the parameters only through the pair $(r, A) = (\beta N - \rho - \mu,\ \rho I_0)$. Hence for fixed $\mu$, every $(\beta, \rho, I_0)$ on the two-dimensional family

$$\beta = \frac{r + \rho + \mu}{N}, \qquad I_0 = \frac{A}{\rho}, \qquad \rho > 0,$$

gives exactly the same early mean case curve, and any likelihood built on early case counts alone (Gaussian, Poisson or negative binomial with mean $\rho I(t)$) is constant along the curve in the $(\beta, \rho)$ plane obtained by varying $\rho$.

The same holds for the pure SIR model $S' = -\lambda S I / N$, $I' = \lambda S I / N - \mu I$ with reported new infections: in the exponential phase $I(t) = I(0) e^{(\lambda - \mu) t}$, so only the effective growth rate $\lambda^* = \lambda - \mu$ (and an amplitude) is identified, and the maximum of the likelihood over the $(\lambda, \mu)$ plane is attained along a line of constant $\lambda - \mu$.

Consequences:

- the basic reproduction number $\beta N / (\rho + \mu)$ (respectively $\lambda / \mu$) is not identified by early case data, since it varies along the family while $r$ is fixed; it is identified only through prior information on the removal rates or on the reporting fraction;
- once depletion of susceptibles matters, the members of the family separate: peak height, epidemic size and duration differ substantially, while the peak time is comparatively insensitive;
- because a likelihood that is flat along a curve has infinitely many maximizers, nonlinear least squares and elementary random-walk samplers converge poorly; the posterior concentrates on a strip rather than a point.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Setting $S = N$ in the infected equation leaves the linear ODE $I' = (\beta N - \rho - \mu) I$, whose solution is $I_0 e^{r t}$; the observable mean $\rho I_0 e^{r t}$ is a two-parameter exponential, so any reparametrization preserving $r$ and $\rho I_0$ preserves the whole early curve. Dehning et al. observed the corresponding equipotential line for $\lambda$ and $\mu$ in a systematic likelihood scan of Germany's initial phase; Roda et al. found the analogous linkage between $\beta$ and $\rho$ in posterior samples for Wuhan, and showed that two equally likely endpoints of the linkage curve predict epidemics of very different scale with nearly the same peak time. In the same data the corrected Akaike criterion $\mathrm{AIC}_c = -2 \ln L(\hat\theta) + 2K + 2K(K+1)/(N_{\mathrm{obs}} - K - 1)$ preferred the SIR model over an SEIR model with two extra unidentified parameters.

## Sources

- W. C. Roda, M. B. Varughese, D. Han and M. Y. Li, "Why is it difficult to accurately predict the COVID-19 epidemic?", Infectious Disease Modelling (2020), Eqs. (2)–(3) and the section on nonidentifiability between transmission rate and diagnosis rate, <https://doi.org/10.1016/j.idm.2020.03.001> (PMC7104073).
- J. Dehning, J. Zierenberg, F. P. Spitzner, M. Wibral, J. P. Neto, M. Wilczek and V. Priesemann, "Inferring change points in the spread of COVID-19 reveals the effectiveness of interventions", Science 369 (2020), eabb9789, Eq. (2) and Fig. 1I, <https://doi.org/10.1126/science.abb9789> (PMC7239331).
