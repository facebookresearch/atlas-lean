# Finite-time extinction of the stronger competitor under sublinear interference

Consider the two-species Lotka–Volterra competition model in which the interference term felt by $u$ is sublinear in $u$:

$$
\frac{du}{dt}=a_1u-b_1u^2-c_1u^{p}v,\qquad \frac{dv}{dt}=a_2v-b_2v^2-c_2u v^{q},\qquad 0<p\le1,\ 0<q\le1,
$$

with positive constants $a_i,b_i,c_i$. The classical model is $p=q=1$. For $0<p<1$ the right-hand side is not Lipschitz at $u=0$, so $u$ can reach $0$ in finite time (finite-time extinction, FTE).

**Exclusion case.** Suppose $\dfrac{a_1}{a_2}>\max\Bigl\{\dfrac{b_1}{c_2},\dfrac{c_1}{b_2}\Bigr\}$, so that in the classical model $(a_1/b_1,0)$ attracts every positive solution and $u$ excludes $v$. Take $q=1$.

*(1)* There is $p\in(0,1)$ for which an interior saddle equilibrium $E_3$ exists. The $u$-nullcline $v=u^{1-p}(a_1-b_1u)/c_1$ crosses the unchanged $v$-nullcline.

*(2)* **Theorem (FTE of the stronger competitor).** Let $0<p<1$ and let $u(0)>0$, $v(0)>0$ with $u(0)\le a_1/b_1$. If

$$
v(0)>f(u(0)),\qquad f(u)=\frac{a_1c_2+(1-p)a_1b_1}{(1-p)\,c_1b_1}\,u^{1-p},
$$

then $u$ goes extinct in finite time and the trajectory approaches $(0,a_2/b_2)$. If instead $(u(0),v(0))$ lies below the stable manifold $W^s(E_3)$, the trajectory converges to $(a_1/b_1,0)$.

So the classically dominant species loses from initial conditions where the weaker species starts abundant enough.

**Weak-competition case.** If $\dfrac{b_1}{c_2}>\dfrac{a_1}{a_2}>\dfrac{c_1}{b_2}$ (classical global coexistence), $0<p<1$ and $q=1$, the same sufficient condition $v(0)>f(u(0))$ forces finite-time extinction of $u$ and convergence to $(0,a_2/b_2)$. Data below the stable manifold of the interior saddle converge to the stable interior equilibrium. Bistability replaces global coexistence.

**FTE in the weaker species.** In the exclusion case with $p=1$, there is $q\in(0,1)$ for which two interior equilibria appear, a saddle and a nodal sink, so the weaker species can avoid exclusion.

## Depends on

- [Explicit solution of the logistic equation](../../../logistic-growth-equation/logistic.md)

## Expansion

Since $u\le a_1/b_1$ is preserved, comparison gives $\dot v\ge -b_2v^2-(a_1c_2/b_1)v$, so $v$ decays at most exponentially, with rate $a_1c_2/b_1$. Dividing the $u$-equation by $u^p$ gives the Bernoulli inequality $\tfrac{d}{dt}u^{1-p}\le(1-p)a_1u^{1-p}-(1-p)c_1v$. Integrating against the exponential lower bound on $v$ shows that $u^{1-p}$ reaches $0$ in finite time once $u(0)^{1-p}$ is below a multiple of $v(0)$, which is the condition $v(0)>f(u(0))$. The nullcline arguments for the interior equilibria use only the intermediate value theorem and linearization at interior points, where the vector field is smooth. The paper also states PDE analogues for the diffusive model with Neumann conditions: FTE can reverse diffusion-induced extinction, and a slower diffuser can lose for suitable $p<1$.

## Sources

- R. D. Parshad, K. Antwi-Fordjour, E. M. Takyi, "Some 'counterintuitive' results in two species competition", arXiv preprint (2020), Section 2 (Lemmas 2.1–2.2, Theorems 2.3–2.4) and Section 3 (PDE case), <https://doi.org/10.48550/arXiv.2008.02704>.
