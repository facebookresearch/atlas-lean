# Lower bound on the first-passage density of a suprathreshold Ornstein–Uhlenbeck neuron

**Setting.** The membrane potential of a stochastic leaky integrate-and-fire neuron between spikes is modelled by the Ornstein–Uhlenbeck process

$$dX = -\beta X\,dt + \sigma\,dW, \qquad X(0) = x_0,$$

with $\beta, \sigma, x_0 > 0$ and $W$ a standard Wiener process. Fix a threshold $\theta$ with $x_0 > \theta > 0$ (the process starts above threshold and relaxes towards $0$), and let $\rho_X(t)$ be the density of the first passage time $\inf\{t : X(t) = \theta\}$.

**Theorem.** Let

$$K = \frac{512}{9\pi}\Big(\frac{x_0}{\theta} - 1\Big), \qquad H = \frac{\beta}{32}\Big(\frac{\theta}{\sigma}\Big)^2,$$

$$u = \frac{1}{2\beta}\log\Big[1 + \Big\{8 \vee \Big(1 + \frac{x_0^2}{\theta^2}\Big) \vee \frac{8\sigma^2}{\beta\theta^2}\Big\}\Big].$$

Then for all $t > u$,

$$\rho_X(t) > k\exp\big[-p\,e^{6\beta t}\big], \qquad k = 2\beta K, \quad p = 1 + H.$$

## Proof sketch

With the exponential time change $s = e^{2\beta t} - 1$, Doob's representation $X(t) = e^{-\beta t}\big(x_0 + \frac{\sigma}{\sqrt{2\beta}}B(e^{2\beta t} - 1)\big)$ shows that $X$ stays above $\theta$ up to time $t$ iff the standard Brownian motion $B$ stays above the square-root boundary $b(s) = \frac{\sqrt{2\beta}}{\sigma}(\theta\sqrt{s+1} - x_0)$ up to $s$, so $\rho_X(t) = 2\beta e^{2\beta t} g(e^{2\beta t} - 1)$ with $g$ the first-passage density of $B$ to $b$. For $s$ large, the density $g(s')$ is bounded below by conditioning on $B$ passing through two intermediate points and bounding quadratic forms in the Gaussian transition densities, giving $g(s') > K s'^{-6}\exp(-H s'^3)$; the polynomial prefactor is absorbed into the double exponential. A strictly positive lower bound on the first-passage density makes the phase-transition kernel of a periodically forced stochastic integrate-and-fire neuron satisfy a Doeblin-type condition, hence asymptotic stability of the phase distribution (Lasota–Mackey criterion).

## Sources

- Peter J. Thomas, "A Lower Bound for the First Passage Time Density of the Suprathreshold Ornstein-Uhlenbeck Process", *Journal of Applied Probability* 48 (2011), 420–434, <https://doi.org/10.1239/jap/1308662636>. Preprint version: arXiv:1101.3915 (2011), Theorem 1 and Section 3, <https://doi.org/10.48550/arXiv.1101.3915>.
