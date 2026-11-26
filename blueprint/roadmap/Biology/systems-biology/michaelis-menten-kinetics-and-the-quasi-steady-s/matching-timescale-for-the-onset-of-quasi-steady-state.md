# Matching timescale for the onset of quasi-steady state

**Setting.** For $E + S \rightleftharpoons C \to E + P$ with initial substrate $s^0$, enzyme $e^0$, Michaelis constant $K_M = (k_{-1}+k_2)/k_1$ and maximal rate $V = k_2e^0$, the classical scaling uses the **fast (characteristic) timescale** of complex build-up and the **slow timescale** of substrate depletion,

$$t_c = \frac{1}{k_1(K_M + s^0)}, \qquad t_s = \frac{s^0}{\max|\dot s|} = \frac{K_M + s^0}{V},$$

and the small parameter $\varepsilon = t_c/t_s$.

**Classification.** A characteristic timescale gives the order of magnitude of the time over which a variable changes appreciably; it is not the time at which a regime ends. At $t = t_c$ the complex has only reached about $(1 - e^{-1})$ of its maximum, so $t_c$ does not mark entry into the quasi-steady-state (QSS) regime. For large $s^0/K_M$ the slow timescale $t_s$ is a **completion timescale**: substrate is almost exhausted by $t_s$, so $t_s$ measures the length of the whole reaction.

**Matching timescale.** Let $t_c^*$ be the time at which the complex reaches its maximum, i.e. the trajectory reaches the $c$-nullcline $\{c = e^0s/(K_M + s)\}$ and the outer (QSS) solution becomes valid. Writing the inner solution $c = c^{\max}(1 - e^{-t/t_c})$ in the slow variable $T = t/t_s$ as $c = c^{\max}(1 - e^{-T/\varepsilon})$, the trajectory is within $O(\varepsilon)$ of the slow manifold once $T = \varepsilon|\ln\varepsilon|$, which gives

$$t_c^* \simeq -t_c\ln\varepsilon = t_c\ln\frac{t_s}{t_c}.$$

This **matching timescale** estimates the transition from transient to QSS kinetics far better than $t_c$, and analogous matching timescales (and a lag time) are derived for coupled two-enzyme mechanisms.

## Depends on

- [Michaelis constant](michaelis-constant.md)
- [Quasi-steady-state value of the complex](qss-complex.md)

## Expansion

By Tikhonov–Fenichel theory, if the slow manifold is uniformly asymptotically stable, trajectories approach it exponentially at rate $1/t_c$ and the outer solution is valid after an initial layer; the layer ends when the exponentially decaying deviation $e^{-t/t_c}$ has fallen to the size $\varepsilon$ of the slow-manifold correction, which happens at $t = t_c|\ln\varepsilon|$. Using $t_c$ itself as the switching time leaves an $O(1)$ relative error in the complex. The logarithmic factor is typical of matched asymptotics and matters in experiment design, where one must wait until $t_c^*$ before reading initial rates.

## Sources

- J. Eilertsen, W. Stroberg, S. Schnell, "Characteristic, completion or matching timescales? An analysis of temporary boundaries in enzyme kinetics", arXiv:1809.03961 (2018), Sections 2–3 (characteristic, completion and matching timescales, Theorem 1) and Sections 4–5 (auxiliary enzyme mechanism), <https://doi.org/10.48550/arXiv.1809.03961>.
