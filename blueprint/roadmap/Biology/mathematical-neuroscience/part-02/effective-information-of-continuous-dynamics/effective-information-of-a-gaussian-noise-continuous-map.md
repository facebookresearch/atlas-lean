# Effective information of a Gaussian-noise continuous map

**Setting.** Let $\mu : \mathbb R^n \to \mathbb R^n$ be a differentiable map (for example, a trained neural network approximating one step of a dynamics) and model the next state as

$$p(Y \mid X) = \frac{1}{(2\pi)^{n/2}|\Sigma|^{1/2}}\exp\Big(-\tfrac12(Y - \mu(X))^{\top}\Sigma^{-1}(Y - \mu(X))\Big), \qquad \Sigma = \mathrm{diag}(\sigma_1^2, \dots, \sigma_n^2).$$

The **effective information** at scale $L$ is the mutual information between input and output when the input is set by the intervention $do(X \sim U([-L, L]^n))$:

$$\mathrm{EI}_L(\mu) = I\big(do(X \sim U([-L,L]^n));\,Y\big).$$

**Theorem.** (i) If $\det \partial\mu(X) \neq 0$ (in the regime where $L$ is large and the noise is small compared with the scale on which $\mu$ varies, with $\mu$ injective on the cube),

$$\mathrm{EI}_L(\mu) \ \approx\ n\ln(2L) + \mathbb E_{X \sim U([-L,L]^n)}\ln\big|\det \partial\mu(X)\big| - \frac{n}{2}\big(1 + \ln(2\pi)\big) - \sum_{i=1}^{n}\ln\sigma_i .$$

(ii) If $\det\partial\mu(X) = 0$ for all $X$, then $\mathrm{EI}_L(\mu) \approx 0$ in the same regime.

**Dimension-averaged quantities.** The dimension-averaged effective information $\mathrm{dEI}_L(\mu) = \mathrm{EI}_L(\mu)/n$ removes the explicit dependence on $n$:

$$\mathrm{dEI}_L(\mu) \approx \ln(2L) + \frac1n\mathbb E\ln|\det\partial\mu(X)| - \frac12\big(1 + \ln(2\pi)\big) - \frac1n\sum_{i}\ln\sigma_i ,$$

and the dimension-averaged causal emergence, the difference of $\mathrm{dEI}$ between a macro-level dynamics and the micro-level dynamics computed with the same $L$, cancels the divergent term $\ln(2L)$.

## Expansion

$I(X;Y) = H(Y) - H(Y \mid X)$. The conditional entropy of a Gaussian with covariance $\Sigma$ is $\frac n2\ln(2\pi e) + \sum_i\ln\sigma_i$, independent of $X$. For small noise, $Y \approx \mu(X)$ with $X$ uniform of entropy $n\ln(2L)$, and the change-of-variables formula for an injective differentiable map gives $H(\mu(X)) = H(X) + \mathbb E\ln|\det\partial\mu(X)|$. Subtracting yields (i). If the Jacobian is everywhere singular, $\mu$ maps the cube onto a lower-dimensional set and the differential-entropy approximation degenerates; the source treats this case as carrying no effective information. Dividing by $n$ and taking differences of macro- and micro-level values removes the dependence on dimension and on $L$.

## Sources

- J. Zhang, K. Liu, "Neural information squeezer for causal emergence", Entropy (2022), Section 3.3.3 (Theorem 1, Eqs. (15)–(18), Definitions 6 and 7) and the appendix proof of Theorem 1, <https://doi.org/10.3390/e25010026>, PMCID PMC9858212.
