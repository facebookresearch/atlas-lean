# Free energy identity for solute diffusion and osmotic water flow across a moving membrane

**Model.** A bounded domain $\Omega\subset\mathbb R^3$ contains a smooth closed deformable membrane $\Gamma_t$ separating the intracellular region $\Omega_i$ from the extracellular region $\Omega_e$. Let $\omega(c_1,\dots,c_N)$ be the entropic free energy density of $N$ uncharged solutes (dilute case $\omega=\sum_k k_BTc_k\ln c_k$), $\mu_k=\partial\omega/\partial c_k$ their chemical potentials, and $\pi_w=\omega-\sum_k c_k\,\partial\omega/\partial c_k$ the entropic part of the water potential (osmotic pressure; $\pi_w=-k_BT\sum_kc_k$ in the dilute case). In $\Omega_i\cup\Omega_e$,

$$
\partial_tc_k+\nabla\cdot(\mathbf uc_k)=\nabla\cdot\Big(c_k\frac{D_k}{k_BT}\nabla\mu_k\Big),\qquad \nu\Delta\mathbf u-\nabla p=0,\quad\nabla\cdot\mathbf u=0 .
$$

On the membrane, with outward normal $\mathbf n$, jump $[w]=w|_{\Gamma_i}-w|_{\Gamma_e}$ and membrane position $\mathbf X(\boldsymbol\theta,t)$:

- solute conservation $c_k(\mathbf u-\frac{D_k}{k_BT}\nabla\mu_k)\cdot\mathbf n=c_k\,\partial_t\mathbf X\cdot\mathbf n+j_k+a_k$ on each face, with passive fluxes obeying $[\mu_k]j_k\ge 0$ and active (pump) fluxes $a_k$;
- force balance $[\Sigma_m(\mathbf u,p)\mathbf n]=\mathbf F_{\mathrm{elas}}$, where $\Sigma_m=\nu(\nabla\mathbf u+\nabla\mathbf u^\top)-p\mathbf I$ and $\mathbf F_{\mathrm{elas}}$ is the variational derivative of a hyperelastic membrane energy $E_{\mathrm{elas}}(\mathbf X)$, so that $\frac{d}{dt}E_{\mathrm{elas}}=-\int_\Gamma\mathbf F_{\mathrm{elas}}\cdot\partial_t\mathbf X\,dm_\Gamma$;
- osmotic slip $\mathbf u-\partial_t\mathbf X=j_w\mathbf n$, with water flux $j_w$ satisfying $[\widehat{\psi_w}]\,j_w\ge 0$, where $\widehat{\psi_w}=\pi_w-\mathbf n\cdot\Sigma_m\mathbf n$ on each face.

No-flux conditions for $c_k$ and $\mathbf u=0$ hold on $\partial\Omega$.

**Theorem (free energy identity).** Smooth solutions satisfy

$$
\frac{d}{dt}\big(G_S+E_{\mathrm{elas}}\big)=-I_p-J_p-J_a,
$$

$$
G_S=\int_{\Omega_i\cup\Omega_e}\omega\,d\mathbf x,\quad I_p=\int_{\Omega_i\cup\Omega_e}\Big(\nu|\nabla\mathbf u|^2+\sum_k c_k\frac{D_k}{k_BT}|\nabla\mu_k|^2\Big)d\mathbf x,
$$

$$
J_p=\int_\Gamma\Big([\widehat{\psi_w}]\,j_w+\sum_k[\mu_k]\,j_k\Big)dm_\Gamma,\quad J_a=\int_\Gamma\sum_k[\mu_k]\,a_k\,dm_\Gamma .
$$

Since $I_p\ge0$ and $J_p\ge 0$ by the passivity conditions, the free energy $G_S+E_{\mathrm{elas}}$ is nonincreasing when there are no active fluxes ($a_k\equiv 0$); pumps are the only terms that can raise it.

## Expansion

Multiply the solute equation by $\mu_k$, integrate over each subdomain, and use the transport theorem on the moving domains; the boundary terms on $\Gamma$ combine, through the solute flux condition, into $\sum_k[\mu_k]\,(j_k+a_k)$ plus a term $-\pi_w\cdot\mathbf n$. Testing Stokes with $\mathbf u$ gives viscous dissipation and the boundary work $[\Sigma_m\mathbf n]\cdot\mathbf u$; force balance and the hyperelastic identity turn the part along $\partial_t\mathbf X$ into $-\frac{d}{dt}E_{\mathrm{elas}}$, and the slip condition leaves $[\mathbf n\cdot\Sigma_m\mathbf n]j_w$. Adding the two leaves exactly $[\widehat{\psi_w}]j_w$; the requirement that this cancellation work is what forces the definition of $\pi_w$ as minus the Legendre transform of $\omega$. Under zero flow, $[\widehat{\psi_w}]=[p-k_BT\sum_kc_k]$, the van 't Hoff statement that water moves down the difference of mechanical and osmotic pressure.

## Sources

- Y. Mori, C. Liu, R. S. Eisenberg, "A Model of Electrodiffusion and Osmotic Water Flow and its Energetic Structure" (2011), Section 2, Theorem 2.1. <https://doi.org/10.48550/arXiv.1101.5193>
