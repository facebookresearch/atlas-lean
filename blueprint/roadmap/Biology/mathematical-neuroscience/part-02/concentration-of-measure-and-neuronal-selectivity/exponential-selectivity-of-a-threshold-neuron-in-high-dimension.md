# Exponential selectivity of a threshold neuron in high dimension

**Setting.** Information items $x_1, \dots, x_M$ (background) and $x_{M+1}$ (relevant) are i.i.d. uniform in the unit ball $B_n(1) \subset \mathbb{R}^n$. A neuron with synaptic weights $w \in \mathbb{R}^n$ and threshold $\theta \ge 0$ responds to $x$ when $\langle w, x\rangle > \theta$ (output $f(\langle w, x\rangle - \theta)$ with $f$ zero on $(-\infty, 0]$ and positive otherwise); it is *silent* on $x$ otherwise. It is *selective* to $x_{M+1}$ if it responds to $x_{M+1}$ and is silent on all background items.

**Theorem.** Let $(w, \theta)$ satisfy $\langle w, x_{M+1}\rangle > \theta$ and $0 < \theta < \|w\|$. Then

$$\mathbb{P}\big(\text{silent on all } x_1, \dots, x_M \mid w, \theta\big) \ge \Big(1 - \tfrac12\big(1 - \theta^2/\|w\|^2\big)^{n/2}\Big)^{M}.$$

Moreover, with $w^* = x_{M+1}/\|x_{M+1}\|$ and $0 < D < \min\{\tfrac12, \|x_{M+1}\|\}$, every pair in

$$\Omega_D = \big\{(w, \theta) : \|w - w^*\| < D,\ D \le \|x_{M+1}\| - \theta \le 2D\big\}$$

responds to $x_{M+1}$, and the probability that all such pairs are silent on every background item is at least

$$\max_{\varepsilon \in (0, 1 - 2D)} \big(1 - (1-\varepsilon)^n\big)\Big(1 - \tfrac12\rho(\varepsilon, D)^{n/2}\Big)^{M}, \qquad \rho(\varepsilon, D) = 1 - \Big(\frac{1 - \varepsilon - 2D}{1 + D}\Big)^2 .$$

Since $\Omega_D$ has positive volume, selectivity is robust to small perturbations of $(w, \theta)$.

**Corollary (memory capacity).** For reliability $\phi \in (0,1)$, the largest number $\bar M$ of background items for which the first bound is at least $\phi$ satisfies

$$\bar M \ge \big\lfloor -\ln\phi\,\big(2e^{\alpha n} - 1\big) \big\rfloor, \qquad \alpha = \ln\frac{\|w\|}{\sqrt{\|w\|^2 - \theta^2}} > 0,$$

so it grows at least exponentially in the neuronal dimension $n$.

## Expansion

The set $\{x \in B_n(1) : \langle w, x\rangle > \theta\}$ is a spherical cap at height $h = \theta/\|w\|$, which is contained in half of a ball of radius $\sqrt{1 - h^2}$; its relative volume is therefore at most $\tfrac12(1 - h^2)^{n/2}$, and independence of the $M$ background items gives the first bound. The corollary inverts it with $-\ln(1 - y) \le y/(1-y)$ for $y = \tfrac12 e^{-\alpha n}$. The second statement additionally uses that $\|x_{M+1}\| > 1 - \varepsilon$ with probability $1 - (1-\varepsilon)^n$, which keeps the threshold of every neuron in $\Omega_D$ away from zero. A Hebbian (modified Oja) plasticity rule $\dot w = \alpha\, v(s, w, \theta)\, y\,(s - w y)$ with $y = \langle w, s\rangle$ drives $w$ toward $w^*$ under persistent stimulation, so selective neurons can also be formed by learning. These are blessing-of-dimensionality effects: in low dimension ($n < 6$ in simulations) neurons confuse stimuli, while for a few tens of inputs single-neuron selectivity becomes almost certain.

## Sources

- I. Tyukin, A. N. Gorban, C. Calvo, J. Makarova, V. A. Makarov, "High-Dimensional Brain: A Tool for Encoding and Rapid Learning of Memories by Single Neurons", Bulletin of Mathematical Biology 81 (2019) 4856–4888, Section 3 (Oja-type rule (10), Definition 1, Theorem 1 with bounds (15)–(17), Corollary 1 with (18)), <https://doi.org/10.1007/s11538-018-0415-5>.
