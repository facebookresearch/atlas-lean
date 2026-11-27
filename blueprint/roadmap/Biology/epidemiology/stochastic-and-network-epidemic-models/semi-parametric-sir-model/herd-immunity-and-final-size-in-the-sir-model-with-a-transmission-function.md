# Herd immunity and final size in the SIR model with a transmission function

**Model.** In the semi-parametric SIR (SPSIR) model the scalar transmission rate is replaced by a function $a:(0,1]\to(0,\infty)$ of the susceptible fraction:

$$\dot x=-a(x)\,y,\qquad \dot y=a(x)\,y-cy,\qquad \dot z=cy,$$

where $x,y,z$ are the susceptible, infected and recovered proportions ($x+y+z=1$) and $c>0$ is the recovery rate. The classical SIR model is $a(x)=\beta x$. A decreasing $a(x)/x$ captures heterogeneous "mover–stayer" populations, in which the most exposed are infected first.

**Theorem.** Let $x(0),y(0)>0$.

*(1)* $x$ decreases and $z$ increases to limits; $y(\infty)=1-x(\infty)-z(\infty)$.

*(2)* If $a^{-1}(c)\in(0,x(0))$, the infected proportion rises then falls, peaking when $x=a^{-1}(c)$; if $a^{-1}(c)>x(0)$ (in particular if $c>a(1)$), $y$ decreases from the start.

*(3)* The solution is given implicitly by

$$t=\int_{x(0)}^{x(t)}\frac{dv}{a(v)\Big\{v-x(0)-y(0)-c\int_{x(0)}^{v}\frac{du}{a(u)}\Big\}},\qquad y(t)-y(0)=x(0)-x(t)+c\int_{x(0)}^{x(t)}\frac{du}{a(u)}.$$

*(4)* If $a$ is increasing, there is a unique $v^*\in(0,x(0))$ solving $v^*-x(0)-y(0)-c\int_{x(0)}^{v^*}\frac{du}{a(u)}=0$ if and only if

$$c\int_0^{x(0)}\frac{du}{a(u)}>x(0)+y(0);$$

then herd immunity is reached, only asymptotically, with final susceptible fraction $x(\infty)=v^*$. For an initially almost fully susceptible population the condition reads $c\int_0^1\frac{du}{a(u)}>1$.

*(5)* Suppose $a$ is strictly increasing and $c\int_0^1\frac{du}{a(u)}>1$, with $x(0)=1-\epsilon$, $y(0)=\epsilon$: if $a(1)>c$, $x(\infty)$ tends as $\epsilon\to0$ to the unique root in $(0,1)$ of $v-1-c\int_1^v\frac{du}{a(u)}=0$, which lies below $a^{-1}(c)$; if $a(1)\le c$, $x(\infty)\to1$.

Unlike the classical model, the final size is not a function of the initial reproduction number $a(1)/c$ alone: it depends on the whole transmission function, so it is not robust to small changes of $a$.

## Expansion

Dividing $\dot y$ by $\dot x$ gives $dy/dx=-1+c/a(x)$, which integrates to the relation between $y$ and $x$ in item 3; substituting into $\dot x=-a(x)y$ and separating variables yields the time integral. Herd immunity corresponds to a zero of $y$ as a function of $x$ inside $(0,x(0))$, and monotonicity of $a$ makes this zero unique; the integral $\int dv/(a(v)\{\cdots\})$ diverges at $v^*$, so it is reached only as $t\to\infty$. For $a(x)=\beta x$ item 5 recovers the classical final-size equation $\log x(\infty)=\tfrac{\beta}{c}(x(\infty)-1)$. In the paper the transmission function is then made a stochastic process, which turns the reproduction number, the peak and the final size into random quantities.

## Sources

- Christian Gouriéroux, Yang Lu, "SIR Model with Stochastic Transmission", arXiv:2011.07816 (2020), Section 2, Propositions 1–5 and Corollaries 1–3, <https://doi.org/10.48550/arXiv.2011.07816>.
