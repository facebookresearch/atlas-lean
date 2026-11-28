# Finite-time extinction of the stronger competitor under sublinear interference

Consider the two-species Lotka–Volterra competition model in which the interference term felt by $u$ is sublinear in $u$:

$$
\frac{du}{dt}=a_1u-b_1u^2-c_1u^{p}v,\qquad \frac{dv}{dt}=a_2v-b_2v^2-c_2u v^{q},\qquad 0<p\le1,\ 0<q\le1,
$$

with positive constants $a_i,b_i,c_i$. The classical model is $p=q=1$. For $0<p<1$ the right-hand side is not Lipschitz at $u=0$, so $u$ can reach $0$ in finite time (finite-time extinction, FTE).

**Exclusion case.** Suppose $\dfrac{a_1}{a_2}>\max\Bigl\{\dfrac{b_1}{c_2},\dfrac{c_1}{b_2}\Bigr\}$, so that in the classical model $(a_1/b_1,0)$ attracts every positive solution and $u$ excludes $v$. Take $q=1$.

*(1)* For every $p\in(0,1)$ there is an interior equilibrium $E_3$, where the $u$-nullcline $v=u^{1-p}(a_1-b_1u)/c_1$ crosses the unchanged $v$-nullcline. It is a saddle under the parametric restriction (A.8) of Theorem A.1 (Lemma 2.2).

*(2)* **Theorem (FTE of the stronger competitor).** Let $0<p<1$ and let $u(0)>0$, $v(0)>0$ with $u(0)\le a_1/b_1$. If

$$
v(0)>f(u(0)),\qquad f(u)=\frac{a_1c_2+(1-p)a_1b_1+a_2b_1}{(1-p)\,c_1b_1}\,u^{1-p},
$$

then $u$ goes extinct in finite time and the trajectory approaches $(0,a_2/b_2)$. If instead $E_3$ is a saddle and $(u(0),v(0))$ lies below its stable manifold $W^s(E_3)$, the trajectory converges to $(a_1/b_1,0)$.

So the classically dominant species loses from initial conditions where the weaker species starts abundant enough.

**FTE in the weaker species (Theorem 2.4).** Let $p=1$ and suppose

$$
\frac{a_1}{c_1}>\frac{a_2}{b_2},\qquad a_2^2b_1+2a_2c_1c_2>4a_1b_2c_2 .
$$

Then there is $q^*\in(0,1)$ such that for every $0<q<q^*$ there are two interior equilibria, a saddle and a nodal sink, so the weaker species can avoid exclusion.

## Depends on

- [Explicit solution of the logistic equation](../../../logistic-growth-equation/logistic.md)

## Expansion

Since $u\le a_1/b_1$ is preserved, comparison gives $\dot v\ge -b_2v^2-(a_1c_2/b_1)v$; with $v\le a_2/b_2$, as in the published proof, this gives $\dot v\ge-(a_2+a_1c_2/b_1)v$, so $v$ decays at most exponentially, with rate $a_2+a_1c_2/b_1$. Dividing the $u$-equation by $u^p$ gives the Bernoulli inequality $\tfrac{d}{dt}u^{1-p}\le(1-p)a_1u^{1-p}-(1-p)c_1v$. Integrating against the exponential lower bound on $v$ shows that $u^{1-p}$ reaches $0$ in finite time once $u(0)^{1-p}$ is below a multiple of $v(0)$, which is the condition $v(0)>f(u(0))$. The nullcline arguments for the interior equilibria use only the intermediate value theorem and linearization at interior points, where the vector field is smooth. The weak-competition case $b_1/c_2>a_1/a_2>c_1/b_2$ is explored in the SIAM edition only by simulation (Remark 2.8), with no theorem. The preprint also states PDE analogues for the diffusive model with Neumann conditions: FTE can reverse diffusion-induced extinction, and a slower diffuser can lose for suitable $p<1$.

## Sources

- R. D. Parshad, K. Antwi-Fordjour, E. M. Takyi, "Some 'counterintuitive' results in two species competition", SIAM J. Appl. Math. 81(5) (2021) 1847–1869, Lemma 2.2 with Theorem A.1, Theorem 2.4, Theorem 2.7 (condition (2.13)) and Remark 2.8, <https://doi.org/10.1137/20M1387274>.
- The same authors' preprint, arXiv:2008.02704 (2020), Section 3 (PDE case), <https://doi.org/10.48550/arXiv.2008.02704>.
