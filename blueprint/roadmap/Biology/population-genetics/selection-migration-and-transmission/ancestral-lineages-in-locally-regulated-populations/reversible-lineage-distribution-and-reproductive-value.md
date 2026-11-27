# Reversible lineage distribution and reproductive value in a locally regulated population

**Setting.** Use the isotropic ancestral-lineage generator of a locally regulated population: dispersal covariance $\sigma^2 I$, dispersal mean $\vec b(x)$, fecundity $\gamma$, establishment probability $r$, population density $\varphi$, and

$$\mathcal{L}_\varphi f=\frac{\sigma^2}{2}\,r\gamma\Big(\Delta f+\Big(2\nabla\log(\gamma\varphi)-\frac{2\vec b}{\sigma^2}\Big)\cdot\nabla f\Big).$$

**Stationary population.** If $\varphi_t\equiv\varphi$ is stationary and the dispersal bias is a gradient, $\vec b=\nabla h$, then the lineage motion is reversible with respect to

$$\pi(x)=\frac{\gamma(x)}{r(x)}\,\varphi(x)^2\,e^{-2h(x)/\sigma^2}.$$

Since the long-term reproductive value of a location is proportional to the fraction of lineages from the distant future passing through it, when $\pi$ is integrable the per-capita long-term reproductive value of an individual at $x$ is proportional to $\pi(x)/\varphi(x)=\gamma\varphi e^{-2h/\sigma^2}/r$.

**Travelling wave.** If instead the population is a travelling wave $\varphi(t,x)=w(x-t\mathfrak{c})$ with velocity $\mathfrak{c}$, where $w$ solves

$$\tfrac12 r\sigma^2\Delta(\gamma w)-\vec b\cdot\nabla(\gamma w)+wF+\mathfrak{c}\cdot\nabla w=0,$$

then, in the frame moving with the wave, the lineage is a time-homogeneous diffusion with generator

$$\mathcal{L}f=\tfrac12\sigma^2 r\gamma\Big(\Delta f+2\nabla\log(\gamma w)\cdot\nabla f\Big)+(\mathfrak{c}-r\gamma\vec b)\cdot\nabla f.$$

Lineages are thus pulled towards high-fecundity, high-density regions behind the front while being swept with the moving frame.

## Depends on

- [Ancestral lineage diffusion in a locally regulated population](ancestral-lineage-diffusion-in-a-locally-regulated-population.md)

## Expansion

Write the isotropic generator as $\mathcal{L}f=\frac{1}{\pi}\nabla\cdot(a\,\pi\nabla f)$ with $a=\tfrac12\sigma^2 r\gamma$; matching drifts requires $\nabla\log(a\pi)=2\nabla\log(\gamma\varphi)-2\nabla h/\sigma^2$, i.e. $a\pi\propto\gamma^2\varphi^2e^{-2h/\sigma^2}$, which gives $\pi\propto\gamma\varphi^2e^{-2h/\sigma^2}/r$. An operator in this divergence form is symmetric in $L^2(\pi)$, hence reversible. The factor $\varphi^2$ (one $\varphi$ from where individuals are, one from the drift towards dense, productive regions) is what distinguishes the lineage law from the population density. For the wave, substituting $\varphi(t,x)=w(x-t\mathfrak{c})$ into the time-inhomogeneous generator and changing to moving coordinates removes the time dependence and adds the drift $\mathfrak{c}$.

## Sources

- Alison M. Etheridge, Thomas G. Kurtz, Ian Letter, Peter L. Ralph and Terence Tsui Ho Lung, "Looking forwards and backwards: Dynamics and genealogies of locally regulated populations", Electron. J. Probab. 29 (2024), 1–85, <https://doi.org/10.1214/24-EJP1075>. Numbering follows the arXiv version, arXiv:2305.14488 (2023): Corollaries 2.27 and 2.28, <https://doi.org/10.48550/arXiv.2305.14488>.
