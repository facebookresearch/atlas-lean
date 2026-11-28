# Matching timescale for the onset of quasi-steady state

**Setting.** For $E + S \rightleftharpoons C \to E + P$ with initial substrate $s^0$, enzyme $e^0$, Michaelis constant $K_M = (k_{-1}+k_2)/k_1$ and maximal rate $V = k_2e^0$, the classical scaling uses the **fast (characteristic) timescale** of complex build-up and the **slow timescale** of substrate depletion,

$$t_c = \frac{1}{k_1(K_M + s^0)}, \qquad t_s = \frac{s^0}{\max|\dot s|} = \frac{K_M + s^0}{V},$$

and the small parameter $\varepsilon = t_c/t_s$.

**Theorem (convergence towards the slow manifold).** Consider a fast–slow system $\dot x = f(x,y)$, $\varepsilon\dot y = g(x,y)$ whose critical manifold $M_0 = \{(x,y) : y = h(x),\ x \in D\}$, $g(x,h(x)) = 0$, is uniformly asymptotically stable, with $f$, $g$ and their first two derivatives uniformly bounded in a neighbourhood $N$ of $M_0$. There are constants $\varepsilon_0, b_0, b_1, \Lambda, M > 0$ such that for every initial condition $(x_0,y_0) \in N$ with $\|y_0 - h(x_0)\| \le b_0$ and every $0 < \varepsilon < \varepsilon_0$,

$$\|y(t) - h(x(t))\| \le M\|y_0 - h(x_0)\|e^{-\Lambda t/\varepsilon} + b_1\varepsilon$$

as long as $x(t) \in D$. In particular $\|y(t) - h(x(t))\| \le (Mb_0 + b_1)\varepsilon$ for all such $t \ge \Lambda^{-1}\varepsilon|\ln\varepsilon|$.

**Matching timescale.** In the slow time $T = t/t_s$ the complex is the fast variable, the $c$-nullcline $\{c = e^0s/(K_M + s)\}$ is the critical manifold, and the theorem puts the trajectory within $O(\varepsilon)$ of the nullcline for $T \ge \Lambda^{-1}\varepsilon|\ln\varepsilon|$, that is, for $t \ge \Lambda^{-1}t_c\ln(t_s/t_c)$. The inner solution $c = c^{\max}(1 - e^{-T/\varepsilon})$ relaxes at rate $1$ in the fast time $T/\varepsilon$; with $\Lambda = 1$ this time is the **matching timescale**

$$t_c^* = -t_c\ln\varepsilon = t_c\ln\frac{t_s}{t_c}.$$

## Depends on

- [Michaelis constant](michaelis-constant.md)
- [Quasi-steady-state value of the complex](qss-complex.md)

## Proof sketch

The bound is Tikhonov's theorem in the form of Gradšteĭn and of Berglund and Gentz: uniform asymptotic stability of $M_0$ makes the deviation $y - h(x)$ contract at rate $\Lambda/\varepsilon$ up to an $O(\varepsilon)$ drift of the critical manifold, and $e^{-\Lambda t/\varepsilon} \le \varepsilon$ exactly when $t \ge \Lambda^{-1}\varepsilon|\ln\varepsilon|$.

A characteristic timescale gives the order of magnitude of the time over which a variable changes appreciably; it is not the time at which a regime ends. At $t = t_c$ the complex has only reached about $(1 - e^{-1})$ of its maximum, so $t_c$ does not mark entry into the quasi-steady-state (QSS) regime. For large $s^0/K_M$ the slow timescale $t_s$ is a **completion timescale**: substrate is almost exhausted by $t_s$, so $t_s$ measures the length of the whole reaction.

Using $t_c$ itself as the switching time leaves an $O(1)$ relative error in the complex. The logarithmic factor is typical of matched asymptotics and matters in experiment design, where one must wait until $t_c^*$ before reading initial rates.

## Sources

- Justin Eilertsen, Wylie Stroberg and Santiago Schnell, "Characteristic, completion or matching timescales? An analysis of temporary boundaries in enzyme kinetics", *Journal of Theoretical Biology* 481 (2019), 28–43, <https://doi.org/10.1016/j.jtbi.2019.01.005>. Preprint version: arXiv:1809.03961 (2018), Sections 2–3 (characteristic, completion and matching timescales, Theorem 1) and Sections 4–5 (auxiliary enzyme mechanism), <https://doi.org/10.48550/arXiv.1809.03961>.
