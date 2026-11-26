# Confounding of network transmission and external infection under aggregate observation

In an SEIR epidemic on a dynamic contact network, susceptible $i$ is infected at hazard $\lambda_i(t)=\beta C_i(t)+\xi$. Here $C_i(t)$ is its current number of infectious contacts, $\beta$ the within-network transmission rate and $\xi$ the external infection pressure. Let $P_\theta^O$ be the law of the observed data $O$, for example periodic symptom and contact surveys. The parameter is *structurally identifiable* if $P_\theta^O=P_{\theta'}^O$ implies $\theta=\theta'$. It is *locally identifiable* at $\theta_0$ if this holds for $\theta$ in a neighbourhood of $\theta_0$.

**Louis identity.** If differentiation and integration can be interchanged, the complete-data, observed-data and missing information matrices satisfy

$$
I_C(\theta)=I_O(\theta)+I_M(\theta),
$$

so partial observation costs exactly the information $I_M$ carried by the latent infection times and edges given the data. If $I_C$ is positive definite and $I_M(\theta;\Delta)\to0$ as the observation interval $\Delta\to0$, then $I_O\to I_C$, and local identifiability under complete observation carries over.

**Transmission–external confounding.** Suppose individual infection times and contact histories are unobserved, and the observed-data law depends on the latent process only through the mean exposure of susceptibles $\bar C(t)=N_S(t)^{-1}\sum_{i:X_i(t)=S}C_i(t)$, hence on $(\beta,\xi)$ only through

$$
\lambda_{\rm agg}(t)=\beta\,\bar C(t)+\xi .
$$

Then $\beta$ and $\xi$ are not separately structurally identifiable unless $\bar C(t)$ varies over time in a way that can be identified from $O$. If $N^{-1}I_O^{(N)}(\theta)\to J(\theta)$ in probability with $J$ positive definite, then $\lambda_{\min}(I_O^{(N)})\to\infty$ and $\theta$ is asymptotically identifiable as the population size grows.

## Depends on

- [Complete-data likelihood of an SEIR epidemic on a status-dependent dynamic network](complete-data-likelihood-of-an-seir-epidemic-on-a-status-dependent-dynamic-network.md)

## Expansion

Louis's identity follows by differentiating $\log p_\theta(O)=\log p_\theta(O,Z)-\log p_\theta(Z\mid O)$ twice and taking expectations. If $\bar C$ is constant, any pair $(\beta',\xi')$ with $\beta'\bar C+\xi'=\beta\bar C+\xi$ gives the same aggregate hazard and so the same observed law; a whole line of parameters is unidentifiable. Exposure variation over time, such as network rewiring or growing prevalence, separates the slope $\beta$ from the intercept $\xi$.

## Sources

- M. Asaduzzaman, "Identifiability and Information-Based Inference for Epidemic Transmission Models Under Partial Observation", arXiv:2607.23079 (2026), Definitions 1–2, Theorems 1–3 and Proposition 1. <https://doi.org/10.48550/arXiv.2607.23079>
