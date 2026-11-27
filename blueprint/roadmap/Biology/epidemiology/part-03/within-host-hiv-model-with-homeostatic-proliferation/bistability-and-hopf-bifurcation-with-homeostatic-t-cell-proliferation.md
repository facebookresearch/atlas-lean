# Bistability and Hopf bifurcation in an HIV model with homeostatic T-cell proliferation

**Model.** Healthy CD4+ T-cells $T$, infected cells $I$ and virions $V$ satisfy

$$
T'=\lambda+\frac{\rho}{C+V}TV-kTV-d_TT,\qquad I'=kTV-d_II,\qquad V'=pI-d_VV,
$$

where $\lambda$ is the T-cell source, $\rho TV/(C+V)$ is homeostatic proliferation stimulated by virus with saturation constant $C$, $k$ the infection rate, $p$ the burst rate and $d_T,d_I,d_V$ death and clearance rates. Rescaling time by $d_T$ and the populations gives the dimensionless system

$$
T'=R_0+\frac{R_m}{1+\beta V}TV-TV-T,\qquad I'=\alpha_1(TV-I),\qquad V'=\alpha_2(I-V),
$$

$$
R_0=\frac{\lambda kp}{d_Td_Id_V},\quad R_m=\frac{\rho}{Ck},\quad \alpha_1=\frac{d_I}{d_T},\quad \alpha_2=\frac{d_V}{d_T},\quad \beta=\frac{d_T}{Ck},
$$

with $R_0$ the usual within-host basic reproduction number and $R_m$ a proliferation reproduction number.

**Theorem (steady states, Theorem 3.1).** The only equilibria are the infection-free state $E_u=(R_0,0,0)$ and

$$
E_i^{\pm}=\Bigl(1,\ \overline V_\pm,\ \overline V_\pm\Bigr),\qquad \overline V_\pm=\frac{-b\pm\sqrt{b^2-4ac}}{2a},\quad a=\beta,\ b=1-R_m+\beta(1-R_0),\ c=1-R_0 ,
$$

whenever these components are real and positive. For $R_0>1$ exactly one infected equilibrium $E_i^+$ is positive; for $R_0<1$ two positive infected equilibria exist when $b<0$ and $b^2>4ac$.

**Theorem (local stability, Theorem 4.1).** $E_u$ is locally asymptotically stable if $R_0<1$ and unstable if $R_0>1$. Whenever $E_i^-$ is positive it is unstable. $E_i^+$ is locally asymptotically stable if

$$
\frac{\alpha_1\alpha_2}{1+\beta\overline V_+}\bigl[\beta\overline V_+^2+R_0-1\bigr]<(\alpha_1+\alpha_2)R_0(\alpha_1+\alpha_2+R_0)
$$

and unstable otherwise. Hence for $R_0<1$ with two infected equilibria and the condition above satisfied, viral clearance $E_u$ and persistent infection $E_i^+$ are both locally asymptotically stable (bistability), and the outcome depends on the initial viral load and T-cell count. Two infected equilibria with $R_0<1$ do not by themselves give bistability: with $\alpha_1=40$, $\alpha_2=240$, $\beta=0.73$, $R_0=0.5$, $R_m=10$ both are positive ($\overline V_+\approx11.77$) but the condition fails, so $E_i^+$ is unstable; the source claims bistability only in the overlap region of its Fig. 3.

**Theorem (Hopf bifurcation, appendix).** For $R_0>1$ there is a critical $R_m^*$ at which two eigenvalues of the Jacobian at $E_i^+$ are purely imaginary and the third is real and negative; as $R_m$ crosses $R_m^*$, $E_i^+$ loses stability and a stable limit cycle branches off.

## Expansion

At equilibrium $I=V$ and $TV=I$, so $T=1$ whenever $V\neq0$, and substituting into the $T$ equation gives $R_0+R_mV/(1+\beta V)-V-1=0$, i.e. the quadratic $\beta V^2+bV+c=0$. At $E_u$ the Jacobian is block triangular with eigenvalue $-1$ and the $(I,V)$ block of determinant $\alpha_1\alpha_2(1-R_0)$, giving the threshold. At $E_i^\pm$ the characteristic polynomial $\eta^3+d_2\eta^2+d_1\eta+d_0$ has $d_0$ proportional to $\beta\overline V^2+R_0-1$ times the slope of the quadratic at $\overline V$; this is negative at the smaller root, so $E_i^-$ has a positive real eigenvalue, and positive at $\overline V_+$ (Lemma: $\beta\overline V_+^2+R_0-1>0$). The Routh–Hurwitz condition $d_1d_2>d_0$ then reduces to the displayed inequality, and its failure through equality, with $d_0>0$, gives the transversal crossing of a complex pair at $R_m^*$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Hurwitz criterion for $2 \times 2$ real matrices](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/hurwitz-criterion-for-two-by-two-matrices.md)
- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Sources

- S. Pankavich, N. Neri and D. Shutt, "Bistable dynamics and Hopf bifurcation in a refined model of early stage HIV infection", arXiv:1910.06280 (2019), Section 2 (model and dimensionless system), Theorem 3.1, Theorem 4.1 and the appendix proof of the stability theorem (lemmas on $d_0$, real roots and $R_m^*$; Hopf theorem), <https://doi.org/10.48550/arXiv.1910.06280>.
