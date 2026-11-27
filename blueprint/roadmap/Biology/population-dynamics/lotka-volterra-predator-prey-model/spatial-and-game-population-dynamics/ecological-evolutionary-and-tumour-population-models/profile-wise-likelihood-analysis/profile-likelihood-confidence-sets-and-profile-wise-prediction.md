# Profile-likelihood confidence sets and profile-wise prediction intervals

Let $\ell(\theta \mid y)$ be the log-likelihood of a parametric model with parameter $\theta \in \Theta \subseteq \mathbb R^p$ for data $y$, with finite supremum, and let $\hat\ell(\theta) = \ell(\theta\mid y) - \sup_{\theta'}\ell(\theta'\mid y)$ be the normalized log-likelihood. Partition $\theta = (\psi, \omega)$ into an interest parameter $\psi$ of dimension $k$ and a nuisance parameter $\omega$. The **profile log-likelihood** is

$$\hat\ell_p(\psi) = \sup_{\omega \mid \psi} \hat\ell(\psi, \omega),$$

and $\Omega^*(\psi) = \{\omega : \hat\ell(\psi, \omega) = \hat\ell_p(\psi)\}$ is the set of all nuisance values attaining it, which may be empty or contain several points. For a level $q \in (0,1)$ let $\Delta_{q,k}$ be the $q$-quantile of the $\chi^2_k$ distribution and $\ell^*_k = -\Delta_{q,k}/2$. The full-likelihood confidence set is $\mathcal C_q = \{\theta : \hat\ell(\theta) \ge \ell^*_p\}$, and the profile confidence set for $\psi$ is $\mathcal C_q^\psi = \{\psi : \hat\ell_p(\psi) \ge \ell^*_k\}$; by Wilks' theorem both have asymptotic coverage $q$ under regularity conditions that include identifiability.

For a model prediction $f(\theta)$ (for example a solution curve $t \mapsto C(t;\theta)$), define the **full-likelihood prediction set** $\mathcal P_q = \{f(\theta) : \theta \in \mathcal C_q\}$ and the **profile-wise prediction set** for the partition $(\psi,\omega)$ as $\mathcal P_q^\psi = \{f(\psi, \omega) : \psi \in \mathcal C_q^\psi,\ \omega \in \Omega^*(\psi)\}$, which propagates every tied maximizer. It is the image of the profile confidence set only where the nuisance supremum is attained, that is where $\Omega^*(\psi)$ is nonempty; the source assumes this throughout. The profile-wise analysis (PWA) prediction set is the union $\bigcup_j \mathcal P_q^{\psi_j}$ over a family of interest parameters (for instance all pairs of components).

**Proposition (coverage transfer).** For every data-generating parameter $\theta_0$, $\Pr_{\theta_0}\bigl(f(\theta_0) \in \mathcal P_q\bigr) \ge \Pr_{\theta_0}\bigl(\theta_0 \in \mathcal C_q\bigr)$. Thus the full-likelihood prediction set has at least the actual coverage of the parameter confidence set, whether or not $\theta$ is identifiable, and it is nonempty since $\hat\theta \in \mathcal C_q$ whenever a maximum likelihood estimate $\hat\theta$ exists. This transfers whatever coverage $\mathcal C_q$ has; it gives nominal coverage $q$ only where $\mathcal C_q$ itself has coverage at least $q$, as Wilks' theorem provides asymptotically under its regularity conditions, and it is no calibration result for non-identifiable models.

## Depends on

This node has no prerequisites.

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

The inclusion of events $\{\theta_0 \in \mathcal C_q\} \subseteq \{f(\theta_0) \in \mathcal P_q\}$ gives the coverage bound. Under non-identifiability, $\mathcal C_q$ is typically unbounded along directions on which the likelihood is flat (in the source's simulations the likelihood-ratio sets were conservative there, unlike Wald-type intervals; this is an empirical finding for those models, not a general theorem), but $\mathcal P_q$ can still be narrow when the prediction depends only on identifiable combinations of parameters. Profile-wise sets trade coverage for computation: each $\mathcal P_q^\psi$ requires optimization over $\omega$ only on a $k$-dimensional grid, and the union over bivariate profiles approximates $\mathcal P_q$. The [logistic model with harvesting](../../../../logistic-growth-equation/structural-non-identifiability-of-logistic-growth-with-harvesting.md) is an example, not a prerequisite: for it Simpson and Maclaren (2024, Fig. 5) report that the bivariate PWA union closely matches the full-likelihood prediction interval and that $\mathcal C_{0.95}$ covered the true parameter in 4,900 of 5,000 simulated data sets ($98\%$), above nominal because of the flat likelihood.

## Sources

- M. J. Simpson and O. J. Maclaren, "Making predictions using poorly identified mathematical models", Bulletin of Mathematical Biology (2024), <https://doi.org/10.1007/s11538-024-01294-0>, PMCID PMC11129983 (equations (8)–(10) and Sections 2.2–2.3).
