# Finite-time blow-up in the variable carrying capacity aphid model

**Boom-bust model.** Let $x(t)\ge0$ be aphid density and $h(t)=a\int_0^t x(s)\,ds$ its scaled cumulative density, with constants $a,r>0$. The cumulative-density model

$$\frac{dh}{dt}=ax,\qquad \frac{dx}{dt}=(r-h)x,\qquad h(0)=0,\ x(0)=x_0>0,$$

gives a single-peak (boom-bust) season. The population grows while $h<r$ and declines after $h$ passes $r$.

**Variable carrying capacity model (VCM).** Field data often show several peaks in one season. To model this, the growth term is multiplied by a logistic factor with a periodically varying carrying capacity:

$$\frac{dh}{dt}=ax,\qquad \frac{dx}{dt}=(r-h)\,x\left(1-\frac{x}{k(t)}\right),\qquad k(t)=(k_{\max}-k_{\min})\,\frac{\cos(d\pi t)+1}{2}+k_{\min},$$

with $0<k_{\min}<k_{\max}$ and $d>0$.

**Theorem (finite-time blow-up).** Solutions of the VCM with $x_0>0$ stay nonnegative. If

$$x_0>k_{\max}\left(\frac{r}{a\,k_{\min}}+1\right),$$

then there is $T^*<\infty$ with $\limsup_{t\to T^*}x(t)=+\infty$, and the cumulative density $h$ also blows up at a finite time.

**Proposition (transient multi-peak dynamics without periodic orbits).** In the non-autonomous boom-bust model $\dot h=a(t)x$, $\dot x=(r(t)-h)x$ with positive $T$-periodic $a,r$, there is no positive $T$-periodic solution. There is a finite $T^*$ such that $h(t)>\sup r$ for $t>T^*$, so $x(t)\to0$. Any oscillations of $x$ that follow the periodic forcing occur only on $[0,T^*]$.

## Expansion

In the autonomous boom-bust model, $dx/dh=(r-h)/a$ gives the first integral $x=x_0+(rh-h^2/2)/a$. This is a single hump in $h$ with its peak at $h=r$, so the trajectory has exactly one maximum, and $x$ returns to $0$ as $h\to r+\sqrt{r^2+2ax_0}$. In the VCM, once $h>r$ the factor $(r-h)$ is negative. If at the same time $x>k(t)$, the product $(r-h)\,x\,(1-x/k)$ becomes positive and grows like $hx^2/k_{\max}$. The usual logistic damping $x-x^2/k$ has flipped sign. The stated threshold on $x_0$ keeps $x$ above $k_{\max}(r/(ak_{\min})+1)$ long enough to compare with $y'=\varepsilon y^2$, which blows up in finite time. Numerically, small $a$ leads to blow-up for essentially any positive initial density, so the multi-peak VCM is structurally unstable. A remedy is an adaptive model that switches to the boom-bust law before the blow-up time. In the non-autonomous model, $\dot h=a(t)x>0$ makes $h$ strictly increasing, which rules out periodicity and eventually forces decay.

## Sources

- Aniket Banerjee, Urvashi Verma, Satyam Narayan Srivastava and Rana D. Parshad, "An investigation of novel population models to control aphid outbreaks via a data driven “adaptive” framework", PLOS Ecosystems 1 (2026), e0000039, <https://doi.org/10.1371/journal.pesy.0000039>; numbering as in arXiv:2310.03058: Section 2 (Lemma 2.1, Theorem 2.3, Theorem 2.4, Lemma 2.5), Section 3 (adaptive behavior model), and Section 4 (nonexistence of $T$-periodic solutions and the transient-oscillation lemma).
