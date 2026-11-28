# Well-posedness of Caputo fractional initial value problems

Let $0<\alpha\le 1$ and let ${}^{C}D_t^{\alpha}$ denote the [Caputo derivative](caputo-fractional-derivative.md): for $0<\alpha<1$,

$$
{}^{C}D_t^{\alpha}x(t)=\frac{1}{\Gamma(1-\alpha)}\int_0^t (t-s)^{-\alpha}\,x'(s)\,ds ,
$$

and for $\alpha=1$ the ordinary derivative $x'(t)$.

A compartmental epidemic model of Caputo type is a system ${}^{C}D_t^{\alpha}x(t)=Q(x(t),t)$, $x(0)=x_0\in\mathbb{R}^n$, where $x=(S,I,R,D,\dots)$ collects the compartments.

**Integral equivalence.** For $h\in L^1[0,T]$, the problem ${}^{C}D_t^{\alpha}\Phi=h$, $\Phi(0)=\Phi_0$ has the unique solution

$$
\Phi(t)=\Phi_0+\frac{1}{\Gamma(\alpha)}\int_0^t (t-\zeta)^{\alpha-1}h(\zeta)\,d\zeta .
$$

Consequently a continuous $x$ solves the Caputo system if and only if it solves the Volterra equation

$$
x(t)=x_0+\frac{1}{\Gamma(\alpha)}\int_0^t (t-s)^{\alpha-1}Q(x(s),s)\,ds .
$$

**Local existence and uniqueness.** Suppose $Q$ is continuous on $[0,a_0]\times\overline{B}_b(x_0)$, bounded there by $\|Q\|_\infty\le M$, and Lipschitz in $x$ with constant $L$. Choose $0<a\le a_0$ with

$$
a<\Big(\frac{b\,\Gamma(\alpha+1)}{M}\Big)^{1/\alpha}\qquad\text{and}\qquad \frac{L\,a^{\alpha}}{\Gamma(\alpha+1)}<1 .
$$

Then the operator $\Psi x(t)=x_0+\Gamma(\alpha)^{-1}\int_0^t (t-s)^{\alpha-1}Q(x(s),s)\,ds$ maps the closed set of continuous functions $[0,a]\to\overline{B}_b(x_0)$ into itself and is a contraction in the supremum norm, so the Caputo system has a unique continuous solution on $[0,a]$.

For the fractional SIRD model

$$
{}^{C}D_t^{\alpha}S=-\frac{\beta SI}{N},\quad {}^{C}D_t^{\alpha}I=\frac{\beta SI}{N}-(\gamma+\kappa)I,\quad {}^{C}D_t^{\alpha}R=\gamma I,\quad {}^{C}D_t^{\alpha}D=\kappa I,
$$

the right-hand side is a polynomial, hence locally Lipschitz, and the theorem applies on every bounded ball of initial data.

## Depends on

- [Caputo fractional derivative](caputo-fractional-derivative.md)

## Expansion

Applying the Riemann–Liouville integral $I^{\alpha}$ to both sides and using $I^{\alpha}\,{}^{C}D_t^{\alpha}\Phi=\Phi-\Phi(0)$ gives the integral form. Since $\Gamma(\alpha)^{-1}\int_0^t (t-s)^{\alpha-1}ds=t^{\alpha}/\Gamma(\alpha+1)$, the first condition on $a$ gives $\|\Psi x-x_0\|_\infty\le M a^{\alpha}/\Gamma(\alpha+1)<b$, so $\Psi$ preserves the ball. The same integral bound turns the Lipschitz estimate into $\|\Psi x-\Psi y\|_\infty\le L a^{\alpha}\Gamma(\alpha+1)^{-1}\|x-y\|_\infty$, and the second condition makes $\Psi$ a contraction; Banach's fixed point theorem finishes. The integral kernel $(t-s)^{\alpha-1}$ is the "memory" that distinguishes the Caputo model from its $\alpha=1$ ODE limit.

## Sources

- K. S. Nisar, S. Ahmad, A. Ullah, K. Shah, H. Alrabaiah, M. Arfan, "Mathematical analysis of SIRD model of COVID-19 with Caputo fractional derivative based on real data", *Results in Physics* 21 (2021) 103772. <https://doi.org/10.1016/j.rinp.2020.103772>. PMCID: PMC7831877. (Lemma 1; existence and uniqueness via the operator (12) in the "Main work" section.)
- K. Diethelm, *The Analysis of Fractional Differential Equations*, Lecture Notes in Mathematics 2004, Springer (2010). <https://doi.org/10.1007/978-3-642-14574-2>
