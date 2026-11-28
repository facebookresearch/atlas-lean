# Bulk-surface activator–inhibitor model of Cdc42 polarisation

**Model.** The cell is the ball $\Omega=\{x\in\mathbb R^3:\|x\|_2<R\}$ with membrane $\Gamma=\partial\Omega$. Cytosolic GDI-bound Cdc42 $G$ lives on $\Omega$. Membrane-bound active (GTP) Cdc42 $A$ and inactive (GDP) Cdc42 $I$ live on $\Gamma$. The rates of the five reactions are: influx $k_1G\,(k_{\max}-(A+I))$, dissociation $k_{-1}I$, activation $k_2I$, inactivation $k_{-2}A$ and feedback activation $k_3A^2I$, all with positive constants. The system is

$$\partial_tG=D_G\Delta G\ \text{in }\Omega,\qquad -D_G(\nabla G)^{\mathsf T}n=Q(A,I,G)=k_1G\,(k_{\max}-(A+I))-k_{-1}I\ \text{on }\Gamma,$$

$$\partial_tA=F(A,I)+D_A\Delta_\Gamma A,\qquad \partial_tI=-F(A,I)+Q(A,I,G)+D_I\Delta_\Gamma I\ \text{on }\Gamma,$$

with $F(A,I)=k_2I-k_{-2}A+k_3A^2I$. The flux $Q$ is both a Neumann condition for $G$ and a source for $I$.

**Proposition (mass conservation).** For any reaction terms $F,Q$,

$$\frac{d}{dt}\Bigl(\int_\Omega G\,dx+\int_\Gamma(A+I)\,ds\Bigr)=0 .$$

**Nondimensional and reduced form.** Rescaling by $u=A\sqrt{k_3/k_{-2}}$, $v=I\sqrt{k_3/k_{-2}}$, $V=GR\sqrt{k_3/k_{-2}}$ and $\tau=D_At/R^2$ gives a model with eight dimensionless parameters: $\gamma=R^2k_{-2}/D_A$, $d=D_I/D_A$, $D=D_G/D_A$, $c_1=\frac{k_1}{Rk_{-2}}\sqrt{\frac{k_{-2}}{k_3}}$, $c_{-1}=k_{-1}/k_{-2}$, $c_2=k_2/k_{-2}$, $c_{\max}=k_{\max}\sqrt{k_3/k_{-2}}$ and $V_0$. The source's Table 1 prints $V=\frac{G}{R}\cdot\sqrt{k_3/k_{-2}}$ and $c_1=(k_1/k_{-2})\sqrt{k_{-2}/k_3}$; the page writes $V=GR\sqrt{k_3/k_{-2}}$ and $c_1=\frac{k_1}{Rk_{-2}}\sqrt{\frac{k_{-2}}{k_3}}$, the dimensionally consistent forms from Eqs. (3)–(4) (since $G$ is a volume concentration and $A, I$ are surface concentrations, $c_1 V = (k_1/k_{-2})G$ requires the extra $1/R$ factor). (The PMC rendering of Table 1 drops the square-root signs; without them $F$ rescales to $(k_{-2}^2/k_3)\bigl(c_2v-u+(k_{-2}/k_3)u^2v\bigr)$, not to a multiple of $f$.) The reaction term is $f(u,v)=c_2v-u+u^2v$ on the unit sphere. In the fast-cytosol limit $D\to\infty$, $V$ is spatially uniform and given by the non-local functional

$$V[u+v]=V_0-\frac{1}{|\Omega|}\int_\Gamma(u+v)\,ds,$$

and the model reduces to the two-species surface system

$$\partial_\tau u=\Delta_\Gamma u+\gamma f(u,v),\qquad \partial_\tau v=d\,\Delta_\Gamma v+\gamma\bigl(-f(u,v)+q(u,v,V[u+v])\bigr),$$

where $q(u,v,V)=c_1V\,(c_{\max}-(u+v))-c_{-1}v$.

## Expansion

Mass conservation follows by integrating the equations. The divergence theorem turns $\int_\Omega D_G\Delta G$ into the boundary flux $-\int_\Gamma Q$, which cancels the source $Q$ in the $I$ equation, and $\int_\Gamma\Delta_\Gamma(\cdot)\,ds=0$ on the closed surface. Because the cytosolic pool is finite, recruitment to the membrane depletes it, and this non-local coupling is what allows a single pole to form. The parameter $\gamma$ measures reaction strength relative to diffusion (equivalently, domain area), and $c_2$ collects the activation–inactivation kinetics.

## Sources

- J. Borgqvist, A. Malik, C. Lundholm, A. Logg, P. Gerlee, M. Cvijovic, "Cell polarisation in a bulk-surface model can be driven by both classic and non-classic Turing instability", *npj Systems Biology and Applications* 7:13 (2021), Results, "The reaction–diffusion model of Cdc42 activation", Eqs. (1)–(6) and Table 1, <https://doi.org/10.1038/s41540-021-00173-x>, PMCID PMC7910310.
