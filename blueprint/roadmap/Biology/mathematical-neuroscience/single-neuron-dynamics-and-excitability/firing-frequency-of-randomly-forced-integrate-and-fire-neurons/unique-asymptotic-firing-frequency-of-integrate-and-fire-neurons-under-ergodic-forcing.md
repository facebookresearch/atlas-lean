# Unique asymptotic firing frequency of integrate-and-fire neurons under ergodic forcing

**Model.** The membrane potential $V(t)$ of a pacemaker neuron stays between a lower threshold $V_l$ and an upper (firing) threshold $V_u$, normalized to the unit interval; between spikes

$$\dot V(t) = F\big(\theta_0\cdot t,\, V(t)\big), \qquad V(t^+) = V_r \ \text{ whenever } V(t) = V_u,$$

with rest potential $V_r \in [V_l, V_u)$. The forcing is driven by a measure-preserving flow $\omega$ on a probability space $(\Theta, \mathcal{B}, \mu)$, written $\theta \mapsto \theta\cdot t$, so the dynamics is a random dynamical system (RDS); $F: \Theta \times \mathbb{R} \to \mathbb{R}$ is bounded on $\Theta \times [0,1]$, uniformly Lipschitz in $V$, and satisfies $F(\theta, V_l) \ge 0$. Identifying $[V_l, V_u)$ with the circle $\mathbb{R}/\mathbb{Z}$ makes the neuron a randomly forced circle flow; let $t_n$ be the time of the $n$-th spike from $(\theta_0, x_0)$.

**Theorem.** Suppose $(\Theta, \mathcal{B}, \mu, \omega)$ is ergodic.
1. If $F$ is non-increasing in $V$, there is a real number $\nu$ such that for $\mu$-almost every $\theta_0$ and every $x_0 \in [V_l, V_r)$,

$$\lim_{n\to\infty}\frac{n}{t_n} = \nu,$$

a unique asymptotic firing frequency independent of the initial state.
2. If instead $F(\theta, V_r) > 0$ for all $\theta$, then there is $\nu$ with $\lim_{n\to\infty} t_n/n = \nu$ for $\mu$-a.e. $\theta_0$ and all $x_0 \in [V_l, V_u)$. If moreover $\Theta$ is a compact metric space, $F$ is continuous, $F(\theta, V_u) > 0$ for all $\theta$ and $\omega$ is uniquely ergodic, the limit holds for every initial condition, uniformly in $(\theta_0, x_0)$.

The proofs rest on a fibred rotation number: for an ergodic RDS of orientation-preserving circle homeomorphisms with continuous lifts satisfying a uniform continuity condition, there is $\rho \in \mathbb{R}$ and a full-measure set $\Theta_0$ on which the lifted orbit satisfies $\lim_{t\to\infty} \hat V_t(\theta, x)/t = \rho$ for all $x$.

## Proof sketch

Without reset the voltage flow is a cocycle $\hat V_{t_1+t_2}(\theta, x) = \hat V_{t_2}(\theta\cdot t_1, \hat V_{t_1}(\theta, x))$; with reset and the circle identification, each spike is one full turn, so the spike count up to time $t$ is the integer part of the lifted angle and the firing frequency is the fibred rotation number. Monotonicity of $F$ in $V$ (or positivity at the reset level) makes the time-$t$ maps order preserving, the key hypothesis for the rotation number to exist and to be independent of $x_0$, as in Poincaré's theory for deterministic circle maps and Herman's for quasiperiodic forcing. The result gives a rigorous rate code for pacemaker neurons under random or quasiperiodic input.

## Sources

- T. Jäger, "Neuronal coding of pacemaker neurons -- A random dynamical systems approach", *Communications on Pure and Applied Analysis* 10 (2011), 995–1009, <https://doi.org/10.3934/cpaa.2011.10.995>. Preprint version: arXiv:0903.4664 (2009), model equations (Section 1), Theorems 1.1 and 1.2, Theorem 3.1 (Section 3), Proposition 4.2 (Section 4), <https://doi.org/10.48550/arXiv.0903.4664>.
