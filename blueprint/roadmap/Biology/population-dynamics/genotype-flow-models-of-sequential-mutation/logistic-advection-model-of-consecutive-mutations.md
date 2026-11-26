# Logistic advection model of consecutive mutations

**Model.** Index genotypes by a continuous mutation coordinate $x\ge0$ (number of accumulated mutations) and let $u(x,t)$ be the genotype density. Sequential mutation at rate $v(t)$ is a flux $\Phi=v(t)u$ along the axis, so conservation with a birth-death source $F(u)$ gives
$$\partial_tu+v(t)\,\partial_xu=F(u),\qquad u(x,0)=\varphi(x),\quad u(0,t)=g(t),$$
with local logistic regulation $F(u)=r(x,t)\big(q-u\big)u$ (growth rate $r\ge0$, limiting density $q$); a nonlocal variant subtracts $\gamma\int_0^xu(\xi,t)d\xi$ inside the bracket. Reverse mutations of intensity $\mu^2$ add a diffusive flux, $\Phi=vu-\mu^2\partial_xu$, giving $\partial_tu+v\partial_xu=F(u)+\mu^2\partial_x^2u$.

**Theorem (explicit solution without reverse mutations).** Let $r$ be continuous and non-negative, $\varphi,g$ smooth with $\varphi(0)=g(0)$, $\varphi'(0)=g'(0)$, $q$ constant, and $V(t)=\int_0^tv$ monotone. Let $Z$ solve $\partial_tZ+v(t)\partial_xZ=r(x,t)\,q$, $Z(x,0)=0$. Then:
1. ahead of the mutation front, on $D_1=\{x\ge V(t)\}$,
$$u(x,t)=\frac{q\,\varphi(y_1)}{\varphi(y_1)+\big(q-\varphi(y_1)\big)e^{-Z(x,t)}},\qquad y_1=x-V(t);$$
2. behind it, on $D_2=\{x<V(t)\}$, with $y_2=V^{-1}(V(t)-x)$ the time at which the characteristic left $x=0$,
$$u(x,t)=\frac{q\,g(y_2)}{g(y_2)+\big(q-g(y_2)\big)e^{-Z(x,t)+Z(0,y_2)}} .$$
With a spatially varying limiting density $q(x)$ and $\varphi(0)=g(0)=0$ the same formulas hold with $q$ replaced by $q(y_1)$ or $q(y_2)$ and $Z$ solving $\partial_tZ+v\partial_xZ=q(x)r(x,t)$ along the characteristic.

Thus each characteristic $x-V(t)=\text{const}$ carries an independent logistic trajectory whose effective time is the growth accumulated along it, and the curve $x=V(t)$ separates the region still remembering the initial genotype distribution from the region filled by mutants emitted from the root genotype.

## Depends on

- [Logistic growth equation](../logistic-growth-equation/README.md)

## Expansion

Along characteristics $dx/dt=v(t)$ the PDE reduces to the logistic ODE $\dot u=r\,(q-u)\,u$, whose solution from $u_0$ is $qu_0/(u_0+(q-u_0)e^{-\int rq})$; the accumulated growth $\int rq$ along the characteristic is exactly $Z$ (or $Z(x,t)-Z(0,y_2)$ for characteristics that started on the boundary). For $v\equiv v_0$ and $r(x)=\delta/(1+x)$ or $r(x)=\delta_1x/(1+\delta_2x^2)$, $Z$ is explicit in logarithms. Decaying mutation rates $v_0e^{-\alpha t}$ give a bounded front $V(\infty)=v_0/\alpha$, so the population saturates within a finite mutational distance, whereas accelerating rates spread it indefinitely. With $\mu>0$ the equation becomes quasilinear parabolic; numerically the backward flux smooths and stabilizes the fronts. Without competition and with linear fitness this framework reduces to quasispecies or Crow-Kimura-type mutation-selection dynamics on a continuous genotype axis.

## Sources

- A. Bratus, T. Yakushkina, V. Posvyanski, "Flow-based modelling of population dynamics with consecutive continuous mutations", arXiv:2512.08660 (2025), Section 2 (model and source terms), Section 3 (Theorem 1 and explicit $Z$), Section 5 (Theorem 2) and Section 6, <https://doi.org/10.48550/arXiv.2512.08660>.
