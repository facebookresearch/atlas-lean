# Cottrell equation

After a potential step fixes the surface concentration of a diffusing reactant, semi-infinite planar diffusion gives the error-function profile and a current proportional to $t^{-1/2}$: $I(t)=neA(c_0-c_1)\sqrt{D/(\pi t)}$.

Let a reactant with diffusion coefficient $D>0$ and initial uniform number concentration $c_0$ fill the
half-space $x>0$ in front of a planar electrode of area $A$ at $x=0$, and let a potential step at $t=0$ fix
the surface concentration at $c_1$ for $t>0$, the electrode reaction transferring $n>0$ electrons per reactant, with $A>0$.
Consider solutions $c$ that are $C^{2,1}$ on $(0,\infty)\times(0,\infty)$, bounded, with

$$\partial_tc=D\,\partial_x^2c\ (x>0,\ t>0),\qquad \lim_{t\to0^+}c(x,t)=c_0\ (x>0),\qquad \lim_{x\to0^+}c(x,t)=c_1\ (t>0),$$

(the data are incompatible at the corner $(0,0)$ when $c_1\ne c_0$, so no continuity there is required). Then

$$c(x,t)=c_1+(c_0-c_1)\operatorname{erf}\!\Big(\frac{x}{2\sqrt{Dt}}\Big),$$

and the current carried by the diffusive flux of reactant into the electrode, $I(t)=neAD\,\partial_xc(0^+,t)$
(positive when the reactant is consumed, $c_0>c_1$), is

$$I(t)=neA\,(c_0-c_1)\sqrt{\frac{D}{\pi t}}\qquad(t>0).$$

For $c_1\ne c_0$, $|I(t)|\to\infty$ as $t\to0^+$ (an artefact of an instantaneous step) and $|I|$ decays as $t^{-1/2}$;
for $c_1=c_0$ the current is zero, and $c_1=0$ gives the diffusion-limited current of a potential step.

## Context

Graduate electrochemistry. Chronoamperometry (and the related potentiostatic intermittent titration technique) uses the $t^{-1/2}$ law to measure diffusion coefficients in battery electrodes.

## Depends on

None.

## Proof depends on

- [Fundamental solution of the heat equation](../../../Analysis/partial-differential-equations/heat-equation/heat-kernel.md)

## Expansion

Proof idea (Lecture 19, Sec. 2.1): the similarity variable $x/(2\sqrt{Dt})$ reduces the problem to an ordinary differential equation solved by $\operatorname{erf}$, and $\partial_x\operatorname{erf}(x/2\sqrt{Dt})|_{x=0}=1/\sqrt{\pi Dt}$ gives the current. Missing prerequisite in the graph: existence and uniqueness, in the bounded class above, for the one-dimensional heat equation on the half-line with Dirichlet boundary data (existing pages cover the whole line and bounded domains only). The existing whole-line results assume continuous initial data, while the odd reflection of $c-c_1$ has a jump at $x=0$ when $c_1\ne c_0$, so they do not apply. A good expansion verifies the explicit profile directly ($\partial_xc=2(c_0-c_1)\Phi(Dt,x)$ with $\Phi$ the one-dimensional heat kernel, and the boundary and initial limits), proves uniqueness in the bounded class, and then computes the surface flux.

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 19: Transient diffusion, Sec. 2.1 (Cottrell equation: boundary conditions, error-function solution and current). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec19.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
