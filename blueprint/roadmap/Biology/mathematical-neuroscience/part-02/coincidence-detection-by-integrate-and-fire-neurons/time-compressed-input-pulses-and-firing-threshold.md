# Time-compressed input pulses and firing threshold

**Leaky integrate-and-fire target.** Let $v'=-v/\tau+I(t)$ for $v<1$, with reset to $0$ at threshold $1$, $\tau>0$. Let $I$ be continuous with $I\ge0$, $I(t)\to0$ as $t\to\infty$ and total charge $q=\int_0^\infty I(t)\,dt\in(0,\infty)$. For $\varepsilon>0$ set $I_\varepsilon(t)=\varepsilon^{-1}I(t/\varepsilon)$ (same charge, delivered in time of order $\varepsilon$; smaller $\varepsilon$ models more synchronous input), let $v_\varepsilon$ solve $v_\varepsilon'=-v_\varepsilon/\tau+I_\varepsilon$, $v_\varepsilon(0)=0$, and $M_\varepsilon=\max_{t\ge0}v_\varepsilon(t)$.

- Scaling identity: $v_\varepsilon(t,\tau)=v_1(t/\varepsilon,\tau/\varepsilon)$.
- $M_\varepsilon$ is strictly decreasing in $\varepsilon$, with $M_\varepsilon\to q$ as $\varepsilon\to0$ and $M_\varepsilon\to0$ as $\varepsilon\to\infty$.
- **Theorem.** If $q>1$ there is $\varepsilon_0>0$ such that $I_\varepsilon$ elicits an action potential iff $0<\varepsilon\le\varepsilon_0$; if $q\le1$, no $I_\varepsilon$ elicits one.

**Theta (quadratic integrate-and-fire) target.** For $v'=-v(1-v)/\tau+I_\varepsilon$, $v(0)=0$, firing means $v$ reaching $+\infty$, and $M_\varepsilon$ is the supremum of $v_\varepsilon$ (infinite if it blows up). If $q>1$ there is $\varepsilon_0>0$ with $M_\varepsilon=\infty$ for $\varepsilon<\varepsilon_0$, $M_{\varepsilon_0}=1$ and $M_\varepsilon<1$ for $\varepsilon>\varepsilon_0$; if $q\le1$ then $M_\varepsilon<1$ for all $\varepsilon$. The source's Theorem 2 prints "and $M_{\varepsilon_0}<1$ for $\varepsilon>\varepsilon_0$", which contradicts its own $M_{\varepsilon_0}=1$ and does not depend on $\varepsilon$; the page writes $M_\varepsilon$, the only reading under which the clause says that inputs spread over longer times than $\varepsilon_0$ fail to fire, as the theorem's conclusion requires.

**Constant drive.** For $v'=-v/\tau+1/\Delta$, $v(0)=0$, the threshold is reached iff $\Delta<\tau$, at $T_\Delta=\tau\ln\frac{\tau/\Delta}{\tau/\Delta-1}$, after injecting charge $Q_\Delta=T_\Delta/\Delta=\varphi(\tau/\Delta)$ with $\varphi(s)=s\ln\frac{s}{s-1}$ strictly decreasing. So when input stops at threshold crossing, more synchronous input (smaller $\Delta$ or $\varepsilon$) is always more efficient.

## Depends on

- [First hit of the threshold under superthreshold drive](../../leaky-integrate-and-fire-neuron/lif-first-hit.md)

## Expansion

For the leaky neuron, $v(t,\tau)=\int_0^te^{-(t-s)/\tau}I(s)\,ds$ is nondecreasing in $\tau$ (strictly where positive) and its maximum tends to $0$ as $\tau\to0$. The scaling identity turns compression of the input into a reduction of the effective membrane time constant from $\tau$ to $\tau/\varepsilon$, which lowers the peak; as $\varepsilon\to0$ the input becomes $q\delta(t)$ and the peak tends to $q$. The theta neuron argument is the same while $v<1$.

## Sources

- C. Börgers, J. Li, N. Kopell, "Approximate, not perfect synchrony maximizes the downstream effectiveness of excitatory neuronal ensembles", Journal of Mathematical Neuroscience 4 (2014) 10, Sections 2.1–2.2 and 3.1–3.3: Lemmas 1–4, Theorems 1 and 2, Equations (6), (8), (19)–(22), <https://doi.org/10.1186/2190-8567-4-10>, PMCID PMC4916341.
