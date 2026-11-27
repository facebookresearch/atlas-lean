# Recovery translation invariance

Let $F[\Phi, t] \in [0, 1]$ be the fraction of circulating current at time $t \ge 0$ after a flash producing $\Phi$ photoisomerizations at $t = 0$. Fix intensities $0 < \Phi_0 < \Phi_{\max}$ and write $S = \Phi_{\max}/\Phi_0$. The family $\{F[\Phi, \cdot]\}$ obeys **recovery translation invariance (RTI)** on $[\Phi_0, \Phi_{\max}]$ if there are a time $t_0 \ge 0$ and a continuous function $h : [1, S] \to \mathbb{R}$ with $h(1) = 0$ and $h(s) > 0$ for $s > 1$ such that

$$F[s\Phi, t] = F[\Phi, t - h(s)]$$

for every base intensity $\Phi \in [\Phi_0, \Phi_{\max}]$, every $s \ge 1$ with $s\Phi \le \Phi_{\max}$, and every $t$ with $t - h(s) \ge t_0 + h(\Phi/\Phi_0)$; together with complete eventual recovery ($F[\Phi, t] \to 1$ as $t \to \infty$ for every $\Phi \in [\Phi_0, \Phi_{\max}]$) and recovery that is not complete in finite time at the base intensity ($F[\Phi_0, t] < 1$ for all $t \ge t_0$). In words, once the recovery from a saturating flash $\Phi$ is in its invariant phase (from time $t_0 + h(\Phi/\Phi_0)$ on), scaling that flash by $s$ shifts the rest of the recovery to the right by $h(s)$ without changing its shape, with the same shift function $h$ for every base intensity.

**Lemma.** If the family obeys RTI with shift function $h$, then $h(s) = \tau \ln s$ for all $s \in [1, S]$, for a constant $\tau > 0$ with units of time.

**Theorem.** A family of recovery traces obeys RTI on $[\Phi_0, \Phi_{\max}]$ with time $t_0$ if and only if there are a constant $\tau > 0$ and a function $H : [0, x_0] \to [0, 1]$, where $x_0 = \Phi_0 e^{-t_0/\tau}$, with $H(0) = 1$, $H(x) \to 1$ as $x \to 0^+$ and $H(x) < 1$ for $0 < x \le x_0$, such that

$$F[\Phi, t] = H\big(\Phi\, e^{-t/\tau}\big) \qquad \text{whenever } \Phi_0 \le \Phi \le \Phi_{\max} \text{ and } \Phi e^{-t/\tau} \le x_0,$$

that is, whenever $t \ge t_0 + \tau \ln(\Phi/\Phi_0)$. The shift function is then $h(s) = \tau \ln s$.

## Expansion

*Lemma.* Take base $\Phi_0$ and $s_1, s_2 \ge 1$ with $s_1 s_2 \le S$. Shifting $s_1 s_2 \Phi_0$ in one step gives $F[s_1 s_2 \Phi_0, t] = F[\Phi_0, t - h(s_1 s_2)]$; shifting it in two steps, first from base $s_1\Phi_0$ by $s_2$ and then from base $\Phi_0$ by $s_1$, gives $F[\Phi_0, t - h(s_1) - h(s_2)]$, both valid for all large $t$. So $F[\Phi_0, \cdot]$ takes equal values at times differing by $d = h(s_1 s_2) - h(s_1) - h(s_2)$ on some half-line $[T, \infty)$. If $d \ne 0$, iterating gives $F[\Phi_0, v] = F[\Phi_0, v + n|d|] \to 1$ for $v \ge T$, contradicting $F[\Phi_0, v] < 1$ on $[t_0, \infty)$; hence $h(s_1 s_2) = h(s_1) + h(s_2)$. Then $\varphi(x) = h(e^x)$ is continuous and additive on $[0, \ln S]$, so $\varphi(x) = \tau x$, i.e. $h(s) = \tau \ln s$, and $h > 0$ on $(1, S]$ gives $\tau > 0$.

*Theorem.* Given RTI, set $H(0) = 1$ and $H(x) = F[\Phi_0, \tau\ln(\Phi_0/x)]$ for $0 < x \le x_0$, a time $\ge t_0$. For $\Phi = s\Phi_0$ and $t \ge t_0 + \tau \ln s$, RTI from base $\Phi_0$ gives $F[\Phi, t] = F[\Phi_0, t - \tau\ln s] = H(\Phi e^{-t/\tau})$; complete recovery gives $H(x) \to 1$ as $x \to 0^+$, and $F[\Phi_0, \cdot] < 1$ on $[t_0, \infty)$ gives $H < 1$ on $(0, x_0]$. Conversely, if $F$ has this form, the RTI window for base $\Phi$ and scale $s$ is exactly the condition that both $(\Phi, t - \tau\ln s)$ and $(s\Phi, t)$ lie in the region $\Phi e^{-t/\tau} \le x_0$, where $F[s\Phi, t] = H(s\Phi e^{-t/\tau}) = F[\Phi, t - \tau \ln s]$; the recovery conditions follow from those on $H$. Only the restriction of $H$ to $[0, x_0]$ is determined by the traces; in the saturating regime of the source, $H$ is a saturation function decreasing towards $0$.

Biologically, RTI is equivalent to the existence of a transduction intermediate produced in proportion to $\Phi$ and decaying with time constant $\tau$ at long times, followed by an arbitrary saturating nonlinearity; the circulating current itself need not decay with $\tau$.

## Sources

- S. Nikonov, N. Engheta, E. N. Pugh Jr., "Kinetics of recovery of the dark-adapted salamander rod photoresponse", Journal of General Physiology 111(1) (1998) 7–37, Eqs. 1–3, Theorem 1, and Appendix I (Lemma and proof of Theorem 1), <https://doi.org/10.1085/jgp.111.1.7>, PMCID PMC1887775.
