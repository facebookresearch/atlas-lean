# Extinction threshold of the SIRS model with Lévy jumps

**Model.** Let $S_t, I_t, R_t$ be the susceptible, infectious and recovered populations, with recruitment $\Lambda$, transmission $\beta$, natural death $\nu$, recovery $\gamma$ and loss of immunity $\sigma$, all positive. Each compartment is perturbed by an independent Brownian motion $B^j$ of intensity $\lambda_j$ and by a compensated Poisson random measure $\tilde N(dt,dy)$ with Lévy measure $\pi$ on a set $\mathbb{Y}$, with jump sizes $\epsilon_j(y)$:

$$dS_t = (\Lambda - \beta S_{t-}I_{t-} - \nu S_{t-} + \sigma R_{t-})\,dt + \lambda_1 S_{t-}\,dB^1_t + \int_{\mathbb{Y}}\epsilon_1(y)S_{t-}\,\tilde N(dt,dy),$$

$$dI_t = (\beta S_{t-}I_{t-} - (\nu+\gamma)I_{t-})\,dt + \lambda_2 I_{t-}\,dB^2_t + \int_{\mathbb{Y}}\epsilon_2(y)I_{t-}\,\tilde N(dt,dy),$$

$$dR_t = (\gamma I_{t-} - (\nu+\sigma)R_{t-})\,dt + \lambda_3 R_{t-}\,dB^3_t + \int_{\mathbb{Y}}\epsilon_3(y)R_{t-}\,\tilde N(dt,dy).$$

The $\epsilon_j$ are bounded with $1 + \epsilon_j > 0$ and $\int_{\mathbb{Y}}\ln^2(1+\epsilon_j)\,d\pi < \infty$. Define the noise penalty

$$\varphi_2 = \frac{\lambda_2^2}{2} + \int_{\mathbb{Y}}\big(\epsilon_2(y) - \ln(1+\epsilon_2(y))\big)\,\pi(dy) \ \ge\ \frac{\lambda_2^2}{2}$$

and the stochastic threshold

$$\xi = \frac{\beta\Lambda}{\nu}\cdot\frac{1}{\nu+\gamma+\varphi_2}.$$

Without noise, this reduces to the deterministic reproduction number $\xi_0 = \beta\Lambda/(\nu(\nu+\gamma))$.

**Theorem.** For every initial value in $\mathbb{R}^3_+$ there is a unique global nonnegative solution. Assume moreover that, for some $m > 2$, $\nu - \frac{m-1}{2}\max_j\lambda_j^2 - \frac{1}{m}\int_{\mathbb{Y}}\big((1+\max_j\epsilon_j(y))^m - 1 - m\min_j\epsilon_j(y)\big)\,\pi(dy) > 0$ (the source's assumption (g), with the maximum of the $\epsilon_j$ in the power and their minimum in the linear term). Then almost surely

$$\limsup_{t\to\infty}\frac{\ln I_t}{t} \le \frac{\beta\Lambda}{\nu}\Big(1 - \frac{1}{\xi}\Big) = (\nu+\gamma+\varphi_2)(\xi - 1).$$

Hence if $\xi < 1$ the infection goes extinct exponentially fast with probability one. In that case the time averages satisfy $\frac1t\int_0^t S_r\,dr \to \Lambda/\nu$ and $\frac1t\int_0^t R_r\,dr \to 0$ almost surely.

Since $\varphi_2 > 0$ whenever there is any noise in the infectious class, $\xi < \xi_0$. White noise and jumps can therefore eliminate an infection that would persist deterministically.

## Expansion

Apply Itô's formula for jump-diffusions to $\ln I_t$:

$$\ln I_t = \ln I_0 + \int_0^t\big(\beta S_r - \nu - \gamma - \varphi_2\big)\,dr + \lambda_2 B^2_t + \int_0^t\!\!\int_{\mathbb{Y}}\ln(1+\epsilon_2)\,\tilde N(dr,dy).$$

The two martingale terms are $o(t)$ by the strong law of large numbers for local martingales with bounded quadratic variation growth. The moment condition with $m > 2$ gives $S_t/t \to 0$ and control of the time averages, so $\limsup\frac1t\int_0^t\beta S_r\,dr \le \beta\Lambda/\nu$. This yields the bound. The convexity inequality $x - 1 - \ln x > 0$ is what makes the jump contribution to $\varphi_2$ positive.

## Sources

- A. Tesfay, T. Saeed, A. Zeb, D. Tesfay, A. Khalaf and J. Brannan, "Dynamics of a Stochastic COVID-19 Epidemic Model with Jump-Diffusion", arXiv:2011.06280 (2020), Section 2 (assumptions (c), (e), (g)), Theorems 2 and 3, <https://doi.org/10.48550/arXiv.2011.06280>.
