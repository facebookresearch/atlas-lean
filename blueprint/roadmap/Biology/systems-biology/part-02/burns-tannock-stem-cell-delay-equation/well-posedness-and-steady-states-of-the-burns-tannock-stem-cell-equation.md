# Well-posedness and steady states of the Burns–Tannock stem cell equation

**Model.** The concentration $Q(t)\ge0$ of resting ($G_0$) hematopoietic stem cells obeys the delay differential equation

$$Q'(t)=-\big(\kappa+\beta(Q(t))\big)Q(t)+A\,\beta\big(Q(t-\tau)\big)Q(t-\tau),\qquad \beta(Q)=f\frac{\theta^s}{\theta^s+Q^s},\qquad A=2e^{-\gamma\tau},$$

where cells enter the cycle at the decreasing Hill rate $\beta$ (maximal rate $f$, half-effect level $\theta$, Hill coefficient $s$), differentiate at rate $\kappa$, die by apoptosis at rate $\gamma$ during a cell cycle of duration $\tau$, and double at mitosis. All parameters are positive.

**Theorem (well-posedness).** For every initial function $\varphi\in C([-\tau,0],[0,\infty))$ the equation has a unique solution defined for all $t\ge0$, and there is $M<\infty$ with $Q(t)\in[0,M]$ for all $t\ge0$. Thus the equation defines a dynamical system on the phase space $C([-\tau,0],[0,\infty))$.

**Steady states.** Steady states solve $[(A-1)\beta(Q)-\kappa]Q=0$. The trivial state $Q=0$ always exists and is globally asymptotically stable if $\kappa>f(A-1)$. A positive steady state exists, and is then unique, iff

$$\kappa<f(A-1)\iff\gamma\tau<\ln\frac{2f}{\kappa+f},\qquad\text{in which case}\qquad Q^*=\theta\Big[\frac{f(A-1)}{\kappa}-1\Big]^{1/s},$$

and $Q^*$ decreases in each of $\kappa$, $\gamma$ and $\tau$, tending to $0$ as the inequality becomes equality. Rescaling $\hat t=t/\tau$, $\hat Q=Q/\theta$, $\hat f=\tau f$, $\hat\kappa=\kappa/f$ reduces the six parameters to four ($\hat f,\hat\kappa,s,A$).

## Expansion

Local existence and uniqueness follow from the method of steps: on each interval $[k\tau,(k+1)\tau]$ the delayed term is a known continuous forcing and the equation is a scalar ODE with locally Lipschitz right-hand side. Nonnegativity: if $Q\ge0$ on $[-\tau,t^*]$, then for $t\in(t^*,t^*+\tau)$ the delayed term is nonnegative, and whenever $Q(t)\in(-\theta,0)$ the equation forces $Q'(t)>0$, so $Q$ cannot become negative. The upper bound comes from the boundedness of $\limsup_{t\to\infty}Q(t)$ for nonnegative solutions, a result of Mackey and Rudnicki for a general class of decreasing entry rates that includes the Hill function; a priori boundedness then gives global existence. The steady-state formula follows from $\beta(Q^*)=\kappa/(A-1)$ and monotonicity of $\beta$.

## Proof depends on

- [Solutions of locally Lipschitz ODEs that leave every compact set](../../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md)

## Sources

- D. C. De Souza and A. R. Humphries, *Dynamics of a mathematical hematopoietic stem-cell population model*, arXiv:1712.08308 (2017), Section 2, Theorem 2.1 and the steady-state analysis preceding Section 2.1. <https://doi.org/10.48550/arXiv.1712.08308>
