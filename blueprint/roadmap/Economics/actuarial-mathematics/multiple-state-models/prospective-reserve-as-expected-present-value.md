# The prospective reserve is the conditional expected present value of future cash flows

Let $\tau$ be the remaining lifetime of a life, with continuous hazard rate $\mu$ on $[0, n]$, so that $\mathbb P(\tau > s \mid \tau > t) = \exp\bigl(-\int_t^s \mu\bigr)$ for $t \le s \le n$, and let $\delta$ be a continuous force of interest. Consider a contract on $[0, n]$ that pays a death benefit $b(\tau)$ at time $\tau$ if $\tau \le n$, a continuous survival payment at rate $g(s)$ and receives premiums at rate $\pi(s)$ while the life is alive, and pays an endowment $E$ at $n$ if $\tau > n$; $b$, $g$ and $\pi$ are continuous. Put

$$V(t) = \int_t^n e^{-\int_t^s (\delta + \mu)} \bigl(\mu(s)\, b(s) + g(s) - \pi(s)\bigr)\, ds + e^{-\int_t^n (\delta + \mu)}\, E.$$

Then on $\{\tau > t\}$ the conditional expected present value at $t$ of the future benefits less premiums,

$$\mathbb E\Bigl[e^{-\int_t^\tau \delta}\, b(\tau)\, \mathbf 1\{\tau \le n\} + \int_t^{\tau \wedge n} e^{-\int_t^s \delta}\, \bigl(g(s) - \pi(s)\bigr)\, ds + e^{-\int_t^n \delta}\, E\, \mathbf 1\{\tau > n\} \Bigm| \tau > t\Bigr],$$

equals $V(t)$. This identifies the solution of Thiele's differential equation $V' = \delta V + \pi - g - \mu (b - V)$, $V(n) = E$, with the conditional expected present value under the lifetime law.

## Sources

- D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life Contingent Risks*, Cambridge University Press, Chapter 7 (policy values and Thiele's differential equation)
