# Pitchfork bifurcation of circular inference dynamics

**Generative model.** A hidden binary state $X_t \in \{0,1\}$ (the 3D interpretation) switches as a continuous-time Markov chain with rates $r_{\mathrm{on}}$ ($0 \to 1$) and $r_{\mathrm{off}}$ ($1 \to 0$). It predicts a binary intermediate variable $X_{2D}$ with reliability $w_S = P(X_{3D} = X_{2D}) \in (1/2, 1)$, and $X_{2D}$ generates a scalar sensory signal $S$ that is Gaussian with mean $\pm \mu_{\mathrm{int}}$ and variance $\sigma_{\mathrm{int}}^2$. Let $L_t = \log \frac{P(X_t = 1 \mid S_{0 \to t})}{P(X_t = 0 \mid S_{0 \to t})}$ be the posterior log-odds.

**Exact inference.** The log-odds obey the leaky integrator

$$\frac{dL}{dt} = -\Phi(L) + w_{\mathrm{int}}\, S, \qquad -\Phi(L) = \big(r_{\mathrm{on}} e^{-L} - r_{\mathrm{off}} e^{L}\big) + (r_{\mathrm{on}} - r_{\mathrm{off}}), \qquad w_{\mathrm{int}} = \frac{2\mu_{\mathrm{int}}}{\sigma_{\mathrm{int}}^2}(2w_S - 1).$$

Without input, $L$ relaxes to the unique stable fixed point $L^\ast = \log(r_{\mathrm{on}}/r_{\mathrm{off}})$, the prior.

**Circular inference.** If top-down messages are re-counted as bottom-up evidence with loop strength $a_P \ge 0$ (descending loops) and bottom-up messages are re-counted as prior with strength $a_S \ge 0$ (ascending loops), the dynamics become

$$\frac{dL}{dt} = -\Phi(L) + aL + w^\ast_{\mathrm{int}}\, S, \qquad a = 2 a_P w_S, \qquad w^\ast_{\mathrm{int}} = w_{\mathrm{int}}(1 + 2 w_S a_S).$$

**Proposition (pitchfork).** Let $r_{\mathrm{on}} = r_{\mathrm{off}} = r$ and $S \equiv 0$. Then $-\Phi(L) + aL = -2r\sinh L + aL$, and
- for $a_P < r / w_S$ the only equilibrium is $L = 0$, globally attracting;
- at $a_P = a_P^{\mathrm{PF}} = r / w_S$ a supercritical pitchfork bifurcation occurs;
- for $a_P > r/w_S$ the origin is unstable and there are two symmetric stable equilibria $\pm L_a$, the nonzero roots of $2r \sinh L = aL$, which move apart as $a_P$ grows.

With noisy ambiguous input, $L$ performs noise-driven hopping between the two wells of the potential $V(L) = -\int(-\Phi(L) + aL)\,dL$, producing perceptual alternations.

## Expansion

The filtering equation is the continuous-time forward recursion of a two-state hidden Markov model in log-odds form: the Markov switching contributes $r_{\mathrm{on}}(1 + e^{-L}) - r_{\mathrm{off}}(1 + e^{L})$ and each Gaussian observation adds its log-likelihood ratio, which is linear in $S$ with slope $2\mu_{\mathrm{int}}/\sigma_{\mathrm{int}}^2$ attenuated by the $X_{2D}$ link. Linearizing $-2r\sinh L + aL$ at $0$ gives slope $a - 2r$, which changes sign at $a = 2r$, that is $a_P = r/w_S$; since $\sinh$ is odd with positive cubic term, the bifurcation is a supercritical pitchfork. Ascending loops leave the noiseless equilibria unchanged but multiply the input gain, which raises the effective noise and the alternation rate. With $r_{\mathrm{on}} \ne r_{\mathrm{off}}$ the pitchfork unfolds into an imperfect one favoring one interpretation.

## Sources

- P. Leptourgos, V. Bouttier, R. Jardri, S. Denève, "A functional theory of bistable perception based on dynamical circular inference", PLoS Computational Biology 16(12) (2020) e1008480, Results, Equations (1)-(8), with derivations in S1 and S2 Text, <https://doi.org/10.1371/journal.pcbi.1008480>, PMCID PMC7769606.
