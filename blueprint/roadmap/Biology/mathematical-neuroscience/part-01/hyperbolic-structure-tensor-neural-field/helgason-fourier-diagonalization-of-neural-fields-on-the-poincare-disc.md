# Helgason–Fourier diagonalization of neural fields on the Poincaré disc

A structure tensor is a symmetric positive-definite $2 \times 2$ matrix $T = \Delta\,\tilde T$ with $\Delta = \sqrt{\det T} > 0$ and $\det\tilde T = 1$; the unimodular part is identified with a point $z$ of the Poincaré disc $\mathbb D = \{|z| < 1\}$, with metric $ds^2 = 4|dz|^2/(1 - |z|^2)^2$, distance $d_{\mathbb D}(z, z') = 2\,\mathrm{artanh}\bigl|(z - z')/(1 - \bar z z')\bigr|$ and area element $dm(z)$. Consider the Wilson–Cowan neural field on the disc

$$\partial_t v(z, t) = -v(z, t) + \int_{\mathbb D} w(z; z')\,S_\mu\bigl(v(z', t)\bigr)\,dm(z') + I_{\mathrm{ext}},$$

with a sigmoid $S_\mu$ of gain $\mu$ and a kernel invariant under the isometry group $G = SU(1,1)$, $w(gz, gz') = w(z, z')$, so that $W(z) = w(z, O)$ depends only on $d_{\mathbb D}(z, O)$. Then:

1. the integral term is a group convolution, $\int_{\mathbb D} w(z; z')S_\mu(v(z'))\,dm(z') = (W * S_\mu(v))(z)$;
2. for $b \in \partial\mathbb D$ and $\rho \in \mathbb C$, the hyperbolic plane waves $e_{\rho,b}(z) = e^{(i\rho + 1/2)\langle z, b\rangle}$, where $\langle z, b\rangle$ is the signed distance from $O$ to the horocycle through $z$ tangent at $b$, are eigenfunctions of the Laplace–Beltrami operator with eigenvalue $-(\rho^2 + \tfrac14)$, so the real spectrum of $-\Delta_{\mathbb D}$ is continuous and bounded below by $1/4$;
3. the Helgason–Fourier transform $\tilde f(\rho, b) = \int_{\mathbb D} f(z)\,e_{-\rho,b}(z)\,dm(z)$ is inverted by $f(z) = \frac{1}{2\pi}\int_{\mathbb R}\int_{\partial\mathbb D}\tilde f(\rho, b)\,e_{\rho,b}(z)\,\rho\tanh(\pi\rho)\,d\rho\,db$ for compactly supported smooth $f$, and for $f_1, f_2 \in L^1(\mathbb D)$ with $f_2$ invariant under the rotation group $K$, $\widetilde{f_1 * f_2} = \tilde f_1\,\tilde f_2$ (Proposition 4).

**Periodic hyperbolic waves.** Write points of $\mathbb D$ in horocyclic coordinates as $n_s a_\tau\cdot O$, with $N=\{n_s\}$ the horocyclic subgroup and $A=\{a_\tau\}$ the one-parameter subgroup of $G$. For solutions invariant under $N$ and periodic in $\tau$, $v(t,(\tau+k)\cdot O)=v(t,\tau\cdot O)$ for a fixed period $k$, the field equation becomes $\partial_t v=-v+\chi*S_\mu(v)$ for $v=v(t,\tau)$, $\tau\in\mathbb R$, an ordinary convolution with $\chi(\tau-\tau')=\int_{\mathbb R}w(a_{\tau-\tau'}\cdot O,n_s\cdot O)\,ds$. After shifting the constant basic state to $v_\mu=0$ with $S_\mu'(0)=\mu$, the linearization acts on $e^{i\alpha\tau}$, $\alpha\in\mathbb R$, by multiplication with $\lambda(\alpha)=-1+\mu\tilde\chi(\alpha)$, where $\tilde\chi$ is the complex-valued Fourier transform of $\chi$. The basic state loses stability at the value $\mu_0$ at which $\max_\alpha\mathrm{Re}\,\lambda(\alpha)$ crosses $0$, attained at $|\alpha|=\alpha_c$; when $\mathrm{Im}\,\tilde\chi(\alpha_c)\ne0$, as in the source's Mexican-hat example, the critical eigenvalues are a purely imaginary pair $\pm i\omega_0$, and the bifurcating solutions are waves $v_\mu(\eta t+\tau)$ travelling at constant speed.

## Expansion

Invariance of $w$ lets one write $z' = g\cdot O$ and integrate over $G$, which turns the integral into a convolution. The Helgason–Fourier transform plays the role of the Euclidean Fourier transform, with plane waves replaced by horocyclic waves and the Plancherel density $\rho\tanh(\pi\rho)$; rotation invariance of $W$ makes $\tilde W$ independent of $b$, so the transform diagonalizes the linearization. Because $G$ is non-compact the critical spectrum is continuous and infinitely degenerate, so bifurcating patterns are sought among functions invariant under a discrete subgroup (periodic patterns on a compact quotient, for example a regular octagon) or on a rotation-invariant subdisc, where equivariant bifurcation theory applies.

## Sources

- P. Chossat, "The hyperbolic model for edge and texture detection in the primary visual cortex", Journal of Mathematical Neuroscience 10 (2020) 2, <https://doi.org/10.1186/s13408-020-0079-y>, PMCID PMC6992837. Equations (2)–(4) and (14); Section 4: Proposition 1, Definitions 1–3, Propositions 2–4 and Theorems 2–3; Section 5.2.1, Eqs. (27)–(28).
