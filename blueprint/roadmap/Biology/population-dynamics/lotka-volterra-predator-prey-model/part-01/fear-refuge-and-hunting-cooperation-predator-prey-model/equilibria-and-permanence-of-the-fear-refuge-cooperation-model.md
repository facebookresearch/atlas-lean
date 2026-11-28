# Equilibria and permanence of the fear–refuge–cooperation predator–prey model

**Model.** Prey $N(t)\ge 0$ and predators $P(t)\ge 0$ satisfy

$$\dot N=\frac{r_0N}{1+k_1P}-r_1N-r_2(1+k_2P)N^2-\frac{\alpha\,g(P)\,NP}{a+g(P)\,N},\qquad \dot P=\frac{\alpha_1\alpha\,g(P)\,NP}{a+g(P)\,N}-d_1P-\frac{qEP}{c_1E+c_2P},$$

where $g(P)=(1-mP)(1+cP)$ combines a predator-dependent refuge ($m$) with hunting cooperation ($c$), $k_1,k_2$ measure fear, $\alpha_1\in(0,1)$ is the conversion efficiency and the last term is saturating (Michaelis–Menten) harvesting with effort $E$. All parameters are positive; the model is used on $0\le P<1/m$, where $g>0$.

**Theorem (boundary equilibria).**

(1) The positive quadrant is invariant, and the extinction equilibrium $E_0=(0,0)$ always exists, with Jacobian eigenvalues $r_0-r_1$ and $-(d_1+q/c_1)$. It is stable if $r_0<r_1$ and unstable if $r_0>r_1$.

(2) The prey-only equilibrium $E_1=(N_1,0)$ with $N_1=(r_0-r_1)/r_2$ exists iff $r_0>r_1$; so $E_0$ and $E_1$ exchange stability through a transcritical bifurcation at $r_0=r_1$.

(3) At $E_1$ the eigenvalues are $-(r_0-r_1)$ and the predator invasion rate

$$\lambda_P=\frac{\alpha_1\alpha N_1}{a+N_1}-d_1-\frac{q}{c_1}.$$

Hence $E_1$ is locally asymptotically stable if $\lambda_P<0$, i.e. if $(r_0-r_1)\,[c_1(d_1-\alpha\alpha_1)+q]+a r_2\,(c_1d_1+q)>0$, and unstable if $\lambda_P>0$ (the predator can invade when this inequality is strictly reversed); at $\lambda_P=0$ the linearization does not decide. The source's Theorem 1(2) says only that $E_1$ "is stable if the following conditions hold", and prints those conditions as $c_1(d_1-\alpha\alpha_1)-q>0$, $(r_0-r_1)[c_1(d_1-\alpha\alpha_1)-q]+ar_2(c_1d_1-q)>0$; the page writes $+q$ because that is what the eigenvalue $\lambda_P$ above gives: multiplying $\lambda_P<0$ by $c_1r_2(a+N_1)>0$ and substituting $N_1=(r_0-r_1)/r_2$ yields exactly the displayed inequality.

(4) An interior equilibrium $E^*$, when it exists, is locally asymptotically stable if $A_1=-\operatorname{tr}J(E^*)>0$ and $A_2=\det J(E^*)>0$, and unstable if $A_1<0$ or $A_2<0$ (the source's Theorem 1(3) prints "iff"; the page drops the "only if" because at a supercritical Hopf point, such as the source's $r_{0h1}=0.4233$ for its Table 1 values, $A_1=0<A_2$ and $E^*$ is still asymptotically stable); a Hopf bifurcation in a parameter $r_0$ occurs at $r_0^c$ with $A_1(r_0^c)=0$, $A_2(r_0^c)>0$ and transversality $\big(2v^2\,dA_1/dr_0+A_1\,dA_2/dr_0\big)|_{r_0^c}\ne 0$, $v^2=A_2(r_0^c)$.

**Theorem (permanence of the seasonal model).** Let $r_0,k_1,k_2,m,c,E$ be continuous, positive, $\omega$-periodic functions, and write $f^M=\sup f$, $f^L=\inf f$. Every solution with positive initial data satisfies $\limsup N\le M_1=(r_0^M-r_1)/r_2$ and $\limsup P\le 1/m^L$, and the system is permanent if (source Eq. (13))

$$\frac{m^Lr_0^L}{m^L+k_1^M}>r_1+\frac{\alpha}{m^L}\Bigl(1+\frac{c^M}{m^L}\Bigr),\qquad \alpha_1\alpha m_1>(a+M_1)\Bigl(d_1+\frac{q}{c_1}\Bigr),$$

where

$$m_1=\frac{\dfrac{m^Lr_0^L}{m^L+k_1^M}-r_1-\dfrac{\alpha}{m^L}\Bigl(1+\dfrac{c^M}{m^L}\Bigr)}{r_2\Bigl(1+\dfrac{k_2^M}{m^L}\Bigr)}$$

is the lower bound $\liminf N\ge m_1$ obtained in the proof. In words, the minimal fear-reduced prey birth rate (fear evaluated at the predator cap $1/m^L$) must exceed $r_1$ plus the maximal per-capita predation pressure, and predator conversion at the prey lower bound $m_1$ must exceed natural mortality plus maximal harvesting; the proof also gives an explicit positive lower bound for $\liminf P$.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Expansion

At $P=0$ the fear factors equal $1$, $g(0)=1$ and the harvesting term has derivative $q/c_1$, so the Jacobian at $(N,0)$ is upper triangular; its diagonal gives the eigenvalues above. Multiplying $\lambda_P<0$ by $c_1(a r_2+r_0-r_1)>0$ and using $a+N_1=(ar_2+r_0-r_1)/r_2$ yields the explicit inequality. The interior statement is the planar Routh–Hurwitz criterion, and the Hopf condition comes from differentiating the real and imaginary parts of the characteristic roots $\xi^2+A_1\xi+A_2=0$ at $A_1=0$; the first Lyapunov coefficient decides super- or subcriticality. Permanence follows from comparison with logistic equations: dropping negative terms bounds $N$ above, the refuge factor $1-mP$ caps $P$ below $1/m^L$, and bounding fear, predation and harvesting by their extreme seasonal values gives logistic lower comparison equations with positive equilibria under the stated inequalities. (The paper writes the $E_1$ condition with $-q$; the sign above follows from the Jacobian, since harvesting always lowers the predator growth rate.)

## Sources

- Mondal B, Roy S, Ghosh U, Tiwari PK, "A systematic study of autonomous and nonautonomous predator-prey models for the combined effects of fear, refuge, cooperation and harvesting" (2022), model (1), Theorem 1 and Theorem 2 (autonomous model) and Theorem 3 (permanence of the nonautonomous model (12)), <https://doi.org/10.1140/epjp/s13360-022-02915-0>, PMCID PMC9217126.
