# Discrete-time likelihood for a spatial transmission kernel

Let units $i = 1, \dots, n$ have pairwise distances $r_{ij}$ and let a parametric kernel $h_\theta(r) \ge 0$ give the daily infection hazard exerted by an infectious unit on a susceptible unit at distance $r$. Observe, day by day, which units are infectious, and for each unit its fate: infected on day $t_{\mathrm{inf},m}$ (set $M$), culled uninfected on day $t_{\mathrm{cul},l}$ (set $\mathcal C$), or never infected nor culled by the end of observation $t_{\mathrm{end}}$ (set $K$). Define the force of infection on unit $i$ on day $t$,

$$\lambda_i(t) \;=\; \sum_{j \ne i} h_\theta(r_{ij})\, \mathbf 1\{j \text{ infectious on day } t\},$$

and assume that, given the infectious set, each susceptible unit is infected on day $t$ independently with probability $q_i(t) = 1 - e^{-\lambda_i(t)}$. Then the probability that $i$ remains uninfected through day $t$ is $e^{-\Lambda_i(t)}$ with $\Lambda_i(t) = \sum_{s \le t} \lambda_i(s)$, and the log-likelihood of $\theta$ is

$$\ell(\theta) \;=\; -\sum_{k \in K} \Lambda_k(t_{\mathrm{end}}) \;-\; \sum_{l \in \mathcal C} \Lambda_l(t_{\mathrm{cul},l}) \;+\; \sum_{m \in M} \Bigl[\log\bigl(1 - e^{-\lambda_m(t_{\mathrm{inf},m})}\bigr) - \Lambda_m(t_{\mathrm{inf},m} - 1)\Bigr].$$

Maximizing $\ell$ gives the kernel estimate, with confidence regions from the profile likelihood.

## Depends on

- [Unit-level reproduction number from a transmission kernel](unit-level-reproduction-number-from-a-transmission-kernel.md)

## Expansion

The daily escape probabilities multiply: a unit uninfected through day $t$ escaped on every day $s \le t$, each with probability $e^{-\lambda_i(s)}$, giving $e^{-\Lambda_i(t)}$. A unit infected on day $t_{\mathrm{inf}}$ escaped through day $t_{\mathrm{inf}} - 1$ and was then infected, contributing $(1 - e^{-\lambda(t_{\mathrm{inf}})})\, e^{-\Lambda(t_{\mathrm{inf}} - 1)}$; censored units (culled, or still susceptible at the end) contribute only their escape probability up to the censoring day. Independence across units given the infectious history makes the likelihood a product, and taking logarithms gives $\ell$. With the logistic kernel $h(r) = h_0/(1 + (r/r_0)^\alpha)$ fitted to the 2003 Dutch avian influenza epidemic, the estimated hazard was about $2 \times 10^{-3}$ per day between neighbouring farms and fell steeply with distance, and alternative kernel shapes were compared by Akaike's information criterion.

## Sources

- G. J. Boender, T. J. Hagenaars, A. Bouma, G. Nodelijk, A. R. W. Elbers, M. C. M. de Jong, M. van Boven, "Risk maps for the spread of highly pathogenic avian influenza in poultry", *PLoS Computational Biology* 3(4) (2007) e71, Methods, "Parameter Estimation" (Equations 7–11), <https://doi.org/10.1371/journal.pcbi.0030071> (PMC1853123).
