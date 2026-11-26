# Average-growth criterion for permanence under periodic pulses

**Model.** For $x=(x_1,\dots,x_n)\in\mathbb{R}^n_+$, a pulse period $\tau>0$ and pulse factors $h_i>-1$, consider the impulsive Kolmogorov system

$$\frac{dx_i}{dt}=x_if_i(x)\quad(t\ne k\tau),\qquad x_i(k\tau^+)=(1+h_i)\,x_i(k\tau^-),\qquad k\in\mathbb{Z}_+,\ i=1,\dots,n.$$

$h_i\in(-1,0)$ models periodic culling or treatment; $h_i>0$ models pulsed births. Let $\Phi$ be the flow of $\dot x_i=x_if_i(x)$, let $r$ multiply coordinate $i$ by $1+h_i$, and let $\pi(x)=r(\Phi(x,\tau))$ be the stroboscopic map just after a pulse.

**Assumptions.** (A1) each $x_if_i$ is locally Lipschitz; (A2) there is a compact $Q\subset\mathbb{R}^n_+$ with $\pi(Q)\subset Q$ that every orbit of $\pi$ enters. Let $\Gamma=\omega_\pi(Q)$ be the global attractor of $\pi$ and $E=\{x:\prod_ix_i=0\}$ the extinction set. The system is *permanent* if there is $\beta>0$ with $1/\beta<\liminf_{t\to\infty}x_i(t)\le\limsup_{t\to\infty}x_i(t)<\beta$ for all $i$ and all positive initial data.

**Theorem (permanence).** Let $\{M_1,\dots,M_l\}$ be a Morse decomposition of $E\cap\Gamma$ for $\pi$. Suppose that for each $M_k$ there are weights $p_{k1},\dots,p_{kn}>0$ such that every $x\in M_k$ admits $\ell_x\in\mathbb{N}$ with

$$\sum_{i=1}^n p_{ki}\sum_{j=0}^{\ell_x}\int_0^\tau\Big(f_i\big(\Phi(\pi^j(x),s)\big)+\frac{\ln(1+h_i)}{\tau}\Big)\,ds>0.$$

Then the impulsive system is permanent.

**Theorem (robustness).** Under the same condition the system is *robustly permanent*: there are $\delta,\beta>0$ such that every perturbation $(\tilde f,\tilde\tau,\tilde h)$ with $|\tilde f_i-f_i|<\delta$, $|\tilde\tau-\tau|<\delta$, $|\tilde h_i-h_i|<\delta$ (keeping $\tilde\tau>0$, $\tilde h_i>-1$, local Lipschitz continuity and dissipation into a common compact set) is permanent with the same bound $\beta$.

## Expansion

A pulse multiplying $x_i$ by $1+h_i$ once per period adds $\ln(1+h_i)$ to $\ln x_i$, i.e. an average per capita rate $\ln(1+h_i)/\tau$. Writing time modulo $\tau$ as an angle $\theta\in S^1$ turns the impulsive system into an autonomous flow on $\mathbb{R}^n_+\times S^1$ whose per capita rates carry this extra term. The orbit of a boundary point $x$ under that flow is the union of the continuous arcs $L_x$ between pulses; the authors show that $\omega$-limit sets, the global attractor and Morse decompositions of $\pi$ lift to the autonomous flow through these arcs. The criterion is then the Garay-Hofbauer type average Lyapunov condition of Patel and Schreiber for flows with feedback: on every boundary invariant piece some positive combination of species can invade on average, so orbits are pushed away from $E$. Robustness is inherited from the robust version of that criterion.

## Sources

- Eleanor Courcelle, Jane Shaw MacDonald, Swati Patel, "Persistence of n-Species Lotka-Volterra Models with Periodic Pulses", arXiv:2609.09343 (2026), Theorem 3.1 (permanence) and Theorem 3.7 (robust permanence); assumptions A1-A2 in Section 3, <https://doi.org/10.48550/arXiv.2609.09343>
