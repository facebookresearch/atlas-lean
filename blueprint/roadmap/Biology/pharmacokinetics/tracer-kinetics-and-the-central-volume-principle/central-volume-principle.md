# Central volume principle

Let blood flow through a tissue region at rate $F > 0$, with tracer concentrations $c_{\mathrm{in}}(t)$ at the arterial inlet and $c_{\mathrm{out}}(t)$ at the venous outlet, and let $q(t)$ be the amount of tracer in the region, with $q(0) = 0$. Mass balance (Fick's principle) gives $dq/dt = F\,(c_{\mathrm{in}} - c_{\mathrm{out}})$. If the region is linear and time-invariant in the tracer, there is an impulse response $R_F$ such that

$$q(t) = \int_0^t c_{\mathrm{in}}(t - \tau)\, R_F(\tau)\, d\tau = F \int_0^t \big[c_{\mathrm{in}}(\tau) - c_{\mathrm{out}}(\tau)\big]\, d\tau. \tag{3}$$

1. **Initial amplitude equals flow.** If no tracer can traverse the region instantaneously ($c_{\mathrm{out}} = 0$ just after an impulse input), then $R_F(0) = F$.
2. **Residence-time interpretation.** $R(t) = R_F(t)/R_F(0)$ is the probability that a tracer molecule entering at time $0$ is still in the region at time $t$; it is non-increasing, $1 - R(t)$ is the distribution function of the transit time, and $h(t) = -dR/dt$ its density.
3. **Flow from volume and mean transit time.** For a tracer confined to a region of distribution volume $V$, with mean transit time $\mathrm{MTT} = \int_0^\infty t\, h(t)\, dt = \int_0^\infty R(t)\, dt$,

$$F = \frac{V}{\mathrm{MTT}}. \tag{4}$$

## Expansion

With an impulse input $c_{\mathrm{in}} = \delta$, (3) gives $q(t) = R_F(t)$, and the right-hand side shows that just after $t = 0$ the region holds the whole bolus $F \int \delta = F$ while nothing has left yet, so $R_F(0^+) = F$. Integrating the impulse response gives $\int_0^\infty R_F(t)\,dt = F \cdot \mathrm{MTT}$; for a unit step input this is the steady-state tracer content of the region, which equals the distribution volume $V$, giving (4). In first-pass perfusion imaging, $R_F$ is recovered by deconvolving the tissue curve with the arterial input. Pointwise division of Fourier transforms is unstable, so a parametric form is fitted, for example the Fermi function $R_F(t) = A / (\exp((t - \mu)/k) + 1)$. Its shape parameters have no physiological meaning; only its amplitude at $t = 0$ (the flow) does.

## Sources

- M. Jerosch-Herold, "Quantification of myocardial perfusion by cardiovascular magnetic resonance", Journal of Cardiovascular Magnetic Resonance 12 (2010) 57, sections "Central Volume Principle" and "Deconvolution Analysis", Eqs. (3) and (4), <https://doi.org/10.1186/1532-429x-12-57> (PMC2964700).
