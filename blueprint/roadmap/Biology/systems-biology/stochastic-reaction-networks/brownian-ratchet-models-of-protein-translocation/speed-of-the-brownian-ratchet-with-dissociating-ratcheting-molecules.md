# Speed of the Brownian ratchet with dissociating ratcheting molecules

**Model I (broken Brownian ratchet).** A protein threading through a membrane pore is modelled by the translocated length $X_t$, which performs a Brownian motion reflected at a moving lower boundary $R_t\le X_t$. Ratcheting molecules bind to the already-translocated part at rate $\gamma\,dx\,dt$ at each position $x\le X_t$ and each stays bound for an independent $\mathrm{Exp}(\delta)$ time ($\delta\ge0$ is the dissociation rate); $R_t$ is the position of the bound molecule closest to $X_t$, which blocks backward diffusion.

**Theorem (positive speed and scaling).** There are constants $0<c\le C<\infty$, with $c$ depending on $\gamma,\delta$ and $C$ only on $\gamma$, such that almost surely

$$c\le\liminf_{t\to\infty}\frac{X_t}{t}\le\limsup_{t\to\infty}\frac{X_t}{t}\le C,$$

and both limits satisfy the scaling relation $a_{\gamma,\delta}=\gamma^{1/3}a_{1,\delta/\gamma^{2/3}}$. In particular, translocation has positive speed however large the dissociation rate is.

**Model II (Poisson-equilibrium approximation).** When the active blocking molecule dissociates (after an $\mathrm{Exp}(\delta)$ time), the boundary jumps down by an independent $\mathrm{Exp}(\gamma/\delta)$ amount, reflecting a Poisson equilibrium of bound molecules of density $\gamma/\delta$ below it; new molecules bind between $R_t$ and $X_t$ at rate $\gamma$ per unit length.

**Theorem (speed of Model II).** Almost surely,

$$\lim_{t\to\infty}\frac{\widetilde X_t}{t}=-\frac{A'(0)}{2A(0)},$$

where $(A,B)$ solves

$$A''(z)=-2\delta B(z)+2\gamma zA(z),\qquad B'(z)=-A'(z)-\frac\gamma\delta B(z),$$

with $A(0)=\tfrac12$, $B(0)=0$, and $A$ strictly decreasing to $0$ as $z\to\infty$. For $\delta=0$, $A(z)=\mathrm{Ai}\big((2\gamma)^{1/3}z\big)/(2\mathrm{Ai}(0))$ and the speed is $-\frac{\mathrm{Ai}'(0)}{2\mathrm{Ai}(0)}(2\gamma)^{1/3}$, with $\mathrm{Ai}$ the Airy function.

## Expansion

Brownian scaling ($X_{ct}\sim\sqrt c\,X_t$) combined with the binding intensity per unit length and time gives the $\gamma^{1/3}$ law: rescaling space by $\gamma^{-1/3}$ and time by $\gamma^{-2/3}$ maps rate $\gamma$ to rate $1$ and $\delta$ to $\delta/\gamma^{2/3}$. Positivity of the speed follows from a renewal (cumulative process) argument: between boundary changes the gap $X_t-R_t$ is a reflected Brownian motion, and a new molecule binds in the gap with killing rate $\gamma(X_t-R_t)$, which links the increment law to Brownian motion killed at a rate proportional to its position; the stationary increment distribution at jump times is described by the ODE system, whose $\delta=0$ case is the Airy equation $A''=2\gamma zA$. Simulations show Models I and II have nearly equal speeds.

## Sources

- A. Depperschmidt, N. Ketterer, P. Pfaffelhuber, "Realistic extensions of a Brownian ratchet for protein translocation", arXiv:1107.5219: Section 2 (Definitions of Models I and II), theorem "Speed of the broken Brownian ratchet, Model I" (positive speed and scaling), theorem "Speed of the broken Brownian ratchet, Model II" and the following remark ($\delta=0$ Airy case), Sections 3.1 and 4.1 (scaling), Sections 4.2–4.3 (killed Brownian motion and invariant increment law). <https://doi.org/10.48550/arXiv.1107.5219> Published version: Journal of Mathematical Biology (2012), as *A Brownian ratchet for protein translocation including dissociation of ratcheting molecules*, <https://doi.org/10.1007/s00285-012-0519-8>.
