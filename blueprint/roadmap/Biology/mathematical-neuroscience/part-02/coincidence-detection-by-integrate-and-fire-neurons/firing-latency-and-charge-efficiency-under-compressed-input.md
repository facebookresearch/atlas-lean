# Firing latency and charge efficiency under compressed input

**Setting.** Use the [time-compressed pulses](time-compressed-input-pulses-and-firing-threshold.md) $I_\varepsilon(t)=\varepsilon^{-1}I(t/\varepsilon)$ with charge $q>1$ and critical compression $\varepsilon_0$. Let $\hat T_\varepsilon$ be the first firing time (threshold $1$ for the leaky neuron, blow-up for the theta neuron) and $\hat R_\varepsilon=\hat T_\varepsilon/\varepsilon$ the latency measured in units of the input duration.

**Theorem (leaky integrate-and-fire).** $\lim_{\varepsilon\to0}\hat T_\varepsilon=0$, $\lim_{\varepsilon\to\varepsilon_0}\hat T_\varepsilon<\infty$, and $\hat R_\varepsilon$ is strictly increasing on $(0,\varepsilon_0)$.

**Theorem (theta neuron).** $\lim_{\varepsilon\to0}\hat T_\varepsilon>0$ and $\lim_{\varepsilon\to\varepsilon_0}\hat T_\varepsilon=\infty$; hence $\hat R_\varepsilon\to\infty$ at both ends of $(0,\varepsilon_0)$ and is non-monotonic.

**Charge consumed.** If the input stops when the target fires, the charge used is

$$Q_\varepsilon=\int_0^{\hat T_\varepsilon}I_\varepsilon(t)\,dt=\int_0^{\hat R_\varepsilon}I(s)\,ds,$$

which is monotone in $\varepsilon$ iff $\hat R_\varepsilon$ is. For the theta neuron an intermediate degree of synchrony minimizes the charge needed.

**Linearly rising input.** For $v'=-v/\tau+(c/\Delta)\,t$, $v(0)=0$, $c>0$ (a synaptic current building up with pulse interval $\Delta$), the threshold time $\tilde T_\Delta$ solves $e^{-\tilde T_\Delta/\tau}-(1-\tilde T_\Delta/\tau)=\Delta/(c\tau^2)$, and the number of pulses delivered by then satisfies

$$\tilde M_\Delta=\frac{\tilde T_\Delta}{\Delta}\sim\sqrt{2/c}\;\Delta^{-1/2}\quad(\Delta\to0),$$

so perfectly synchronous volleys waste input.

## Depends on

- [Time-compressed input pulses and firing threshold](time-compressed-input-pulses-and-firing-threshold.md)

## Expansion

The leaky scaling identity gives $\hat R_\varepsilon(\tau)=\hat T_1(\tau/\varepsilon)$, monotone because the voltage is monotone in the time constant. For the theta neuron, a $q\delta$ kick above $1$ still needs a positive time to escape to infinity, and at $\varepsilon_0$ the trajectory creeps up to the unstable point $v=1$ without crossing, giving infinite latency. For the ramp, $v(t)\approx ct^2/(2\Delta)$ for $t\ll\tau$, so $\tilde T_\Delta\approx\sqrt{2\Delta/c}$.

## Sources

- C. Börgers, J. Li, N. Kopell, "Approximate, not perfect synchrony maximizes the downstream effectiveness of excitatory neuronal ensembles", Journal of Mathematical Neuroscience 4 (2014) 10, Sections 4.1, 4.2 and 4.4: Theorems 3, 4 and 5, Equations (24)–(29), <https://doi.org/10.1186/2190-8567-4-10>, PMCID PMC4916341.
