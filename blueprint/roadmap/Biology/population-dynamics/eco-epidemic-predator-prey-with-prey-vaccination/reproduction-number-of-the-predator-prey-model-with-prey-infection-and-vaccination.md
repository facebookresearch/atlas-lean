# Reproduction number of the predator–prey model with prey infection and vaccination

**Model.** Prey are split into susceptible $S$, infected $I$ and vaccinated $V$ classes, and $P$ is a predator with Lotka–Volterra (mass-action) functional response. Only susceptible prey reproduce (logistic growth with rate $r$ and capacity $k$, crowded by $S+I$); infection spreads among prey by mass action with rates $\beta$ (susceptible) and $\sigma$ (vaccinated, partially protected); susceptibles are vaccinated at rate $\phi$ and lose protection at rate $\theta$; prey classes emigrate at rates $m_1,m_2,m_3$ and die at rates $d_1,d_2,d_3$, with extra disease mortality $c$; the predator eats class $X$ with search efficiency $p_X$, converts it with efficiency $q_X$, and dies at rate $d_4$:

$$\frac{dS}{dt}=rS\Big(1-\frac{S+I}{k}\Big)-\beta SI-\phi S+\theta V-p_1PS-(m_1+d_1)S,$$

$$\frac{dI}{dt}=\beta SI+\sigma VI-p_2PI-(m_2+d_2+c)I,$$

$$\frac{dV}{dt}=\phi S-\theta V-\sigma VI-p_3PV-(m_3+d_3)V,$$

$$\frac{dP}{dt}=(q_1p_1S+q_2p_2I+q_3p_3V)P-d_4P .$$

All parameters are positive. The nonnegative orthant is invariant, and when the conversion efficiencies satisfy $q_1,q_2,q_3<1$ all solutions are uniformly bounded: $\chi=S+I+V+P$ obeys $\dot\chi+\mu\chi\le k(r+\mu)^2/(4r)$ for any $0<\mu<\min(m_2+d_2+c,\ m_3+d_3,\ d_4)$.

**Disease-free, predator-free equilibrium.** Let

$$\Theta=r-\phi-m_1-d_1+\frac{\theta\phi}{\theta+m_3+d_3}.$$

If $\Theta>0$, there is a unique equilibrium $E_1=(S_1,0,V_1,0)$ with

$$S_1=\frac{k}{r}\,\Theta,\qquad V_1=\frac{\phi}{\theta+m_3+d_3}\,S_1 .$$

**Reproduction number.** By the next-generation method, with new infections $\beta S+\sigma V$ and removal $p_2P+m_2+d_2+c$ evaluated at $E_1$,

$$\mathcal{R}_0=\frac{\beta S_1+\sigma V_1}{c+m_2+d_2}.$$

At $E_1$ the Jacobian is block triangular: the infected direction has eigenvalue $(c+m_2+d_2)(\mathcal{R}_0-1)$ and the predator direction has eigenvalue $q_1p_1S_1+q_3p_3V_1-d_4$. So infection can invade the vaccinated, predator-free prey population exactly when $\mathcal{R}_0>1$; vaccination lowers $\mathcal{R}_0$ by moving prey from $S$ to the less susceptible class $V$ (since $\sigma<\beta$ is the intended regime), and emigration of infected prey ($m_2$) acts like extra removal.

## Expansion

At an equilibrium with $I=P=0$ the $V$ equation gives $V=\phi S/(\theta+m_3+d_3)$, and substituting into the $S$ equation leaves $r(1-S/k)=\phi+m_1+d_1-\theta\phi/(\theta+m_3+d_3)$, which is solvable with $S>0$ iff $\Theta>0$. The infected class is one-dimensional, so the next-generation matrix is the scalar $FV^{-1}=(\beta S_1+\sigma V_1)/(m_2+d_2+c)$, and the threshold statement is the general next-generation theorem: the infected subsystem's linearization at $E_1$ has a positive eigenvalue iff $\mathcal{R}_0>1$. Boundedness follows by adding the four equations, using $q_X<1$ to dominate the predator's gain by the prey losses to predation, and bounding $rS(1-S/k)+\mu S$ by its maximum $k(r+\mu)^2/(4r)$. The paper also gives the predator-only, predator-free endemic and interior equilibria with Routh–Hurwitz conditions for their local stability, and uses Bendixson–Dulac arguments to exclude periodic orbits in two-dimensional coordinate planes.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Sources

- Sachin Kumar, Harsha Kharbanda, "Stability Analysis of Prey-Predator Model with Infection, Migration and Vaccination in Prey", arXiv:1709.10319 (2017): model in Section 2, Theorem 3.1 (uniform boundedness) and the basic reproduction number in Section 3, equilibria and existence conditions in Section 5, Theorem 5.1 and Remark 5.2 (Bendixson–Dulac arguments). <https://doi.org/10.48550/arXiv.1709.10319>
