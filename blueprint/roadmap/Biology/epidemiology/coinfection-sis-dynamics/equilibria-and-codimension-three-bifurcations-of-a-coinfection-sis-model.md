# Equilibria and codimension-three bifurcations of a coinfection SIS model

**Setting.** A population with birth and death rate $b$ is split into susceptibles $S$, individuals infected only with disease 1 ($I_1$, recovering at rate $\theta_1$), only with disease 2 ($I_2$, no recovery), and coinfected individuals $I_m$. Transmission is mass action with rates $\alpha_1,\alpha_2$ for the single infections and $\alpha$ for coinfection; a singly infected individual becomes coinfected by contact with the other single infection or with a coinfected individual, and coinfected individuals also transmit the joint infection to susceptibles. With constant total population, proportions, and rescaled parameters $a_i=\alpha_i/b$, $k=\alpha/b$, $r_1=1+\theta_1/b$, the model reduces to
$$\begin{aligned}\dot I_1&=(a_1-r_1)I_1-a_1I_1^2-(a_1+a_2)I_1I_2-(a_1+k)I_1I_m,\\ \dot I_2&=(a_2-1)I_2-a_2I_2^2-(a_1+a_2)I_1I_2-(a_2+k)I_2I_m,\\ \dot I_m&=(a_1+a_2)I_1I_2+(k-1)I_m-kI_m^2,\end{aligned}$$
on $\{I_1,I_2,I_m\ge0,\ I_1+I_2+I_m\le1\}$. The single-disease reproduction numbers are $a_1/r_1$, $a_2$ and $k$.

**Theorem 1 (boundary equilibria).** The disease-free equilibrium $E_0=(0,0,0)$ always exists; $E_1=((a_1-r_1)/a_1,0,0)$ exists if $a_1>r_1$; $E_2=(0,(a_2-1)/a_2,0)$ exists if $a_2>1$; and $E_3=(0,0,(k-1)/k)$ exists if $k>1$. Theorem 2 adds mixed boundary equilibria $E_{1m}=\bigl((a_1-k^2-(r_1-1)k)/(a_1k),0,(k-1)/k\bigr)$ when $k>1$ and $a_1>r_1k+(k-1)k$, and $E_{2m}=\bigl(0,(a_2-k^2)/(a_2k),(k-1)/k\bigr)$ when $k>1$ and $a_2>k^2$.

**Theorem 5 and Theorem 6 (stability).** $E_0$ is a stable node when all three reproduction numbers are below $1$. $E_1$ is a locally asymptotically stable node when the invasion reproduction number of disease 2 at $E_1$ is below $1$; it is a saddle-node when exactly one of $a_2=a_1(a_1-r_1+1)/r_1$ and $k=1$ holds, and a cusp of codimension $3$ when both hold.

**Theorem 9 (Bogdanov-Takens bifurcation).** At the interior (endemic) equilibrium $E_4$, for $k=1$ and a second explicit degeneracy condition on the parameters, the system undergoes a Bogdanov-Takens bifurcation of codimension $3$, so that multiple limit cycles, homoclinic loops and coexisting endemic states can arise nearby. A saddle-node bifurcation of $E_4$ occurs on another explicit parameter curve (Theorem 8).

## Expansion

Boundary equilibria follow by setting one or two infected classes to zero, which leaves logistic-type equations. Stability of $E_1$ is read off the Jacobian, which is triangular on the invariant face; when two eigenvalues vanish together the centre-manifold reduction has a degenerate quadratic part, giving the codimension-3 cusp. The codimension-3 Bogdanov-Takens point at $E_4$ is found by reducing to normal form with successive near-identity transformations; its unfolding explains bistability between disease-free and endemic states and oscillations seen in simulations, phenomena absent from single-disease SIS models.

## Sources

- Y. Liu, "Study on dynamical behavior of coinfection infectious disease model", arXiv preprint (2025), Theorems 1, 2, 5, 6, 8 and 9, <https://doi.org/10.48550/arXiv.2503.09472>.
