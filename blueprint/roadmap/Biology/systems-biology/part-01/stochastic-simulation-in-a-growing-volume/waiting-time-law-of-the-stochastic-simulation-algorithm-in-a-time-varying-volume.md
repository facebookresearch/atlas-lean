# Waiting-time law of the stochastic simulation algorithm in a time-varying volume

Consider a well-mixed reaction system in state $Y$ at time $t$ inside a container of volume $V(s)$, $s \ge t$, that varies in time while the molecular state stays $Y$ (between reactions). Split the reactions into first-order channels $\mathcal Q_1$, with volume-independent propensities $a_\mu(Y)$, and higher-order channels $\mathcal Q$, with propensities $a_\mu(Y, s) = h_\mu(Y)k_\mu/V(s)^{\ell-1}$ for a reaction of order $\ell \ge 2$. Put $A_{\mathcal Q_1}(Y) = \sum_{\mu\in\mathcal Q_1} a_\mu(Y)$ and $A_{\mathcal Q}(Y, s) = \sum_{\mu\in\mathcal Q} a_\mu(Y, s)$. Then the probability that the next reaction is $R_\mu$ and occurs in $(t+\tau, t+\tau+d\tau)$ is

$$P_\mu(\tau \mid Y, t)\,d\tau = \exp\Bigl[-A_{\mathcal Q_1}(Y)\tau - \int_t^{t+\tau} A_{\mathcal Q}(Y, s)\,ds\Bigr]\,a_\mu(Y, t+\tau)\,d\tau,$$

and the waiting time has distribution function

$$F(\tau \mid Y, t) = 1 - \exp\Bigl[-A_{\mathcal Q_1}(Y)\tau - \int_t^{t+\tau} A_{\mathcal Q}(Y, s)\,ds\Bigr].$$

By inversion, $\tau$ solves $u_1 = F(\tau \mid Y, t)$ for $u_1$ uniform on $[0, 1]$. If the volume is frozen over the step this gives the usual $\tau = -\log(1 - u_1)/(A_{\mathcal Q_1}(Y) + A_{\mathcal Q}(Y, t))$; with the first-order correction $\int_t^{t+\tau}A_{\mathcal Q} \approx A_{\mathcal Q}(Y,t)\tau + \dot A_{\mathcal Q}(Y,t)\tau^2/2$ one obtains

$$\tau = \frac{-(A_{\mathcal Q_1} + A_{\mathcal Q}) + \sqrt{(A_{\mathcal Q_1} + A_{\mathcal Q})^2 - 2\log(1 - u_1)\,\dot A_{\mathcal Q}}}{\dot A_{\mathcal Q}},$$

which has no real solution when $\dot A_{\mathcal Q} < 0$ and $\log(1 - u_1) < (A_{\mathcal Q_1} + A_{\mathcal Q})^2/(2\dot A_{\mathcal Q})$. Then the second-order step is invalid and $\tau$ must be found from $u_1 = F(\tau \mid Y, t)$. No further reaction can occur only if $A_{\mathcal Q_1}(Y) = 0$, and then with probability $\exp\bigl(-\int_t^\infty A_{\mathcal Q}(Y, s)\,ds\bigr)$; if $A_{\mathcal Q_1}(Y) > 0$, then $F(\tau \mid Y, t) \to 1$ as $\tau \to \infty$ and a reaction occurs with probability $1$.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](../../gillespie-direct-method.md)

## Expansion

The no-reaction probability satisfies $P_{\mathrm{not}}(s + ds) = P_{\mathrm{not}}(s)\bigl(1 - \sum_\mu a_\mu(Y, t+s)\,ds\bigr)$, a linear ODE whose solution is the exponential factor; multiplying by the propensity of channel $\mu$ at the end of the interval gives $P_\mu$, and summing and integrating gives $F$ because the integrand is minus the derivative of the exponential. With constant volume all propensities are constant and the direct method is recovered. Since higher-order propensities scale like $1/V$, growth slows bimolecular chemistry, which is how container growth and internal reactions are coupled. The source's Remark 2 reads the missing real root as the volume growing so fast that no reaction can occur; it is an artefact of the truncation, since the truncated exponent $(A_{\mathcal Q_1} + A_{\mathcal Q})\tau + \dot A_{\mathcal Q}\tau^2/2$ has a maximum when $\dot A_{\mathcal Q} < 0$, while the exact exponent $A_{\mathcal Q_1}(Y)\tau + \int_t^{t+\tau} A_{\mathcal Q}(Y, s)\,ds$ is nondecreasing in $\tau$.

## Sources

- T. Carletti and A. Filisetti, "The stochastic evolution of a protocell: the Gillespie algorithm in a dynamically varying volume", Computational and Mathematical Methods in Medicine 2012 (2012) 423627, <https://doi.org/10.1155/2012/423627>, PMCID PMC3318221. Section 3, Equations (4)–(9); Section 4, Proposition 1, Equations (15)–(22) and Remark 2.
