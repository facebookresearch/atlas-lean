# Periodic asymptotics of time-discretized integrate-and-fire networks

For the time-discretized conductance-based integrate-and-fire network $V(t+1) = F(V(t))$ on the compact invariant set $M$, with threshold $\theta$, let

$$\Omega = \bigcap_{t \ge 0} F^t(M)$$

be the $\omega$-limit set (the union of the $\omega$-limit sets of all points), and let the singularity set be $\mathcal S = \{V : V_i = \theta \text{ for some } i\}$. Define the distance from the asymptotic dynamics to the threshold

$$d(\Omega, \mathcal S) = \inf_{V \in \Omega}\ \inf_{t \ge 0}\ \min_{i = 1, \dots, N} |V_i(t) - \theta| . \tag{29}$$

1. **Uniform firing or uniform silence.** Suppose there are $\varepsilon > 0$ and $T < \infty$ such that for every $V \in M$ and every neuron $i$, either $V_i(t) \ge \theta$ for some $t \le T$, or $V_i(t) < \theta - \varepsilon$ for all $t$ from some time $t_0(V, \varepsilon)$ on. Then $\Omega$ consists of finitely many periodic orbits, each of period at most $T$.
2. **Distance to threshold.** If $d(\Omega, \mathcal S) > 0$, then $\Omega$ consists of finitely many periodic orbits of finite period, and each trajectory on $\Omega$ corresponds one-to-one to its raster plot.

An orbit is a *ghost orbit* if some neuron $i$ satisfies $V_i(t) < \theta$ for all $t > 0$ but $\limsup_{t \to \infty} V_i(t) = \theta$; ghost orbits are excluded by either hypothesis. The *edge of chaos* is the set of parameters where $d(\Omega, \mathcal S) = 0$; only there can the dynamics show sensitivity to initial conditions.

## Depends on

- [Piecewise contraction of a time-discretized integrate-and-fire network](piecewise-contraction-of-a-time-discretized-integrate-and-fire-network.md)

## Expansion

Each branch of the flow is an affine contraction, and the diameter of the image of a branch domain shrinks as soon as all neurons that ever fire have fired. Under the hypotheses, the raster plot observed over a window of bounded length determines the future branch sequence, so only finitely many raster prefixes are legal on $\Omega$. Contraction then collapses each of them onto a periodic orbit. A positive distance to the threshold means a small perturbation never moves a neuron across $\theta$, so nearby trajectories share their raster plot and converge to each other, giving the one-to-one coding by spikes. Neurons that stop firing are still driven by the others and oscillate below threshold in the limit. Although the dynamics is periodic away from the edge of chaos, periods can be far longer than any observation time near it. The effective entropy $h^{(\mathrm{eff})} = \frac{1}{T_0}\log n(T_0)$, with $n(T_0)$ the number of legal raster prefixes of length $T_0$, measures this.

## Sources

- B. Cessac, T. Viéville, "On dynamics of integrate-and-fire neural networks with conductance based synapses", *Frontiers in Computational Neuroscience* (2008), Section 3 ("Asymptotic dynamics": Definition 1, Theorem 1; "Ghost orbits": Definition 2; "Edge of chaos": Eq. (29), Theorem 2, Definitions 3–4), <https://doi.org/10.3389/neuro.10.002.2008> (PMC2525942).
