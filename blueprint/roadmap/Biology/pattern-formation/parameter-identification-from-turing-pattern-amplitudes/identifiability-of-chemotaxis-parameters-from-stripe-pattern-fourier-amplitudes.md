# Local identifiability of chemotaxis–logistic parameters from Fourier amplitudes of a stripe pattern

**Models.** On the line, a cell density $n$ with logistic growth is attracted by a chemical $c$ that it produces and that decays:

$$
\text{Model 1:}\quad 0=d_nn''-\chi_0\bigl(n\,c'\bigr)'+rn(1-n),\qquad 0=d_cc''+n-c ;
$$

$$
\text{Model 2:}\quad 0=d_nn''-\chi_0\Bigl(\frac nc\,c'\Bigr)'+rn(1-n),\qquad 0=d_cc''+n-c ,
$$

(density-dependent sensitivity $\chi(n,c)=\chi_0n$, resp. ratio-dependent sensitivity $\chi_0n/c$), with diffusion constants $d_n,d_c>0$, chemotactic coefficient $\chi_0>0$ and growth rate $r>0$. These are the stationary equations of the corresponding chemotaxis systems, whose homogeneous state $n=c=1$ undergoes a Turing instability for strong chemotaxis.

**Theorem (Model 1, Theorem 2.1).** Let $(n,c)$ be a nonconstant stationary periodic solution of Model 1 of the form $n=\sum_{j=0}^3\alpha_j\cos(jkx)$, $c=\sum_{j=0}^3\beta_j\cos(jkx)$ with wavenumber $k>0$, on the nontrivial homogeneous branch $\alpha_0=\beta_0=1$, with $\alpha_1\ne0$, and suppose the amplitudes $\mathcal M_3=\{\alpha_j,\beta_j\}_{j=0}^3$ are observed. Then

$$
C:=d_ck^2=\frac{\alpha_1}{\beta_1}-1,\qquad \beta_j=\frac{\alpha_j}{1+j^2C}\ (j=1,2,3).
$$

Matching the coefficients of $1,\cos kx,\dots,\cos4kx$ gives equations $F_j(D,X,R;C)=0$ in $D=d_nk^2$, $X=\chi_0k^2$, $R=r$, homogeneous in $(D,X,R)$. With $Y=\chi_0/d_n$ and $Z=r/(d_nk^2)$, if the reduced system $\widehat{\mathcal F}_3(Y,C,Z)=0$ has Jacobian of rank $3$ at the observed point, then the scale-invariant quantities

$$
d_ck^2,\qquad \frac{\chi_0}{d_n},\qquad \frac{r}{d_nk^2}
$$

are locally uniquely determined by $\mathcal M_3$. If $d_n$ is known, $d_c k^2$, $\chi_0$ and $r/k^2$ follow; if also $k$ (the observed wavelength $2\pi/k$) is known, $d_c,\chi_0,r$ are locally identifiable.

**Theorem (Model 2, Theorem 2.2).** The same conclusion holds for Model 2 from the two-mode amplitudes $\mathcal M_2=\{\alpha_j,\beta_j\}_{j=0}^2$ of a solution $n=\sum_{j=0}^2\alpha_j\cos(jkx)$, $c=\sum_{j=0}^2\beta_j\cos(jkx)$ with $\alpha_0=\beta_0=1$, $\alpha_1\ne0$, again under a rank-$3$ condition on the reduced system.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/README.md)

## Expansion

The signal equation is linear: projecting $d_cc''+n-c=0$ on $\cos(jkx)$ gives $\beta_j(1+j^2d_ck^2)=\alpha_j$, which yields $C$ from the first mode and all $\beta_j$ from the $\alpha_j$. Substituting the finite Fourier series into the cell equation, the quadratic nonlinearities $(nc')'$ (or the expansion of $c'/c$ in Model 2) and $n^2$ produce products of cosines that reduce to modes up to $\cos4kx$ by product-to-sum formulas; each mode gives one polynomial equation in $(D,X,R)$ with coefficients depending on the observed amplitudes. The equations are homogeneous of degree one in $(D,X,R)$, so only ratios are identifiable from amplitudes alone, and the implicit function theorem under the rank condition gives local uniqueness of $(Y,C,Z)$. Physical scales then require one extra measurement (for example $d_n$ from cell tracking) and the observed stripe spacing.

## Sources

- Y. Li, H. Liu and C. W. K. Lo, "Parameter identification in reaction-diffusion-chemotaxis systems from single Turing pattern amplitudes", arXiv:2509.07458 (2025), Section 2 (Theorems 2.1–2.2) and Sections 3–4 (proofs), <https://doi.org/10.48550/arXiv.2509.07458>.
