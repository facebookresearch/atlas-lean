# Macroscopic bump and its coarse stability in a three-state neural automaton

**Model.** On the ring $\mathbb S=\mathbb R/2L\mathbb Z$ each neuron $x$ is, at discrete time $t$, refractory ($u=-1$), quiescent ($u=0$) or spiking ($u=1$); let $X_k(t)=\{x:u(x,t)=k\}$. With a Mexican-hat kernel $w(x)=A_1\sqrt{B_1/L}\,e^{-4B_1x^2}-A_2\sqrt{B_2/L}\,e^{-4B_2x^2}$, its periodic extension $W$ (maximal at $0$ with $W(0)>0$), and gain $\kappa>0$, the synaptic input is

$$J(x,t)=\kappa\int_{X_1(t)}W(x-y)\,dy .$$

In the deterministic limit (Heaviside firing with threshold $h>0$ and certain recovery) the update is: spiking neurons become refractory, refractory neurons become quiescent, and a quiescent neuron spikes iff $J(x,t)\ge h$:

$$X_{-1}(t+1)=X_1(t),\quad X_0(t+1)=X_{-1}(t)\cup\big(X_0(t)\cap X_<(t)\big),\quad X_1(t+1)=X_0(t)\cap X_\ge(t),$$

where $X_\ge=\{J\ge h\}$ and $X_<$ is its complement.

**Proposition 1 (bump construction).** For $\eta_1<\eta_2$ split $[\eta_1,\eta_2)$ into $3m$ equal strips $A^m_1,\dots,A^m_{3m}$ and let the states $-1,0,1$ occupy the strips cyclically ($X_1^m=\bigcup_jA^m_{3j}$, and so on), with the rest of the ring quiescent. Then the mesoscopic profiles $J_m(x)=\kappa\int_{X^m_1}W(x-y)\,dy$ converge uniformly in $x$ to

$$J_b(x,\eta_1,\eta_2)=\frac{\kappa}{3}\int_{\eta_1}^{\eta_2}W(x-y)\,dy,$$

and if $\Delta\in(0,L)$ satisfies

$$3h=\kappa\int_0^{\Delta}W(y)\,dy,$$

then $J_b(0,0,\Delta)=J_b(\Delta,0,\Delta)=h$: the interval $[0,\Delta]$ is reproduced as its own active set, a macroscopic bump of width $\Delta$.

**Coarse stability.** Track the bump by its threshold crossings $\xi=(\xi_1,\xi_2)$ through the implicit map $J_b(\xi_i(t+1),\xi_1(t),\xi_2(t))=h$, $i=1,2$. Linearizing at $\xi_*=(0,\Delta)$ gives the eigenvalues

$$\lambda_1=1\ \ (v^1=(1,1)^{\top},\ \text{translation}),\qquad \lambda_2=\frac{W(0)+W(\Delta)}{W(0)-W(\Delta)}\ \ (v^2=(-1,1)^{\top},\ \text{width}),$$

so the bump is coarsely stable to width perturbations iff $|\lambda_2|<1$, i.e. iff $W(\Delta)<0$: the bump edges must lie in the inhibitory surround of the kernel.

## Expansion

Within a fully resolved bump every neuron cycles $0\to1\to-1\to0$, so at any time a third of the active region spikes. As $m\to\infty$ the spiking strips equidistribute in $[\eta_1,\eta_2)$, and the Riemann sums $\kappa\sum_j\int_{A^m_{3j}}W(x-y)\,dy$ converge uniformly to one third of the full integral by uniform continuity of $W$; this is the factor $1/3$ in $J_b$. The threshold condition makes the endpoints of $[0,\Delta]$ exactly critical, and by symmetry of $W$ the input exceeds $h$ inside. For stability, implicit differentiation of the threshold conditions gives a $2\times2$ matrix with entries $W(0)$ on the diagonal and $-W(\Delta)$ off it, scaled by $1/(W(0)-W(\Delta))$; the translation mode has eigenvalue one by rotational invariance, and the width mode contracts, monotonically and without alternating sign, exactly when $W(\Delta)<0$. (The source prints $\lambda_1=-1$ and a negative $\lambda_2$; both signs contradict translation invariance.) The same construction yields multi-bump states and travelling waves, which the paper continues numerically in the stochastic network via equation-free methods.

## Sources

- Avitabile D, Wedgwood KCA, "Macroscopic coherent structures in a stochastic neural network: from interface dynamics to coarse-grained bifurcation analysis", J Math Biol (2017), Equations (1)-(18), Proposition 1 and the bump-stability analysis, <https://doi.org/10.1007/s00285-016-1070-9>, PMCID PMC5562874.
