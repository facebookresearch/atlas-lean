# Dispersion relation of the cell–ECM mechanical model

In the [cell–ECM mechanical model](cell-ecm-mechanical-model-with-viscoelastic-matrix.md), every non-trivial homogeneous steady state has $\bar n\equiv1$, $\bar u\equiv0$ and arbitrary $\bar\rho\equiv\rho_0>0$. Put $\lambda_1=1/(1+\lambda)$ and $\lambda_2=(1-\lambda)/(1+\lambda)^2$, and write $A(\psi)=a_2\psi^2+a_1\psi+a_0$ and $B(\psi)=b_2\psi^2+b_1\psi+b_0$ for the symbols of $\mathcal L_a$ and $\mathcal L_b$.

**Homogeneous perturbations.** Perturbations proportional to $e^{\psi t}$ with $\psi\ne0$ satisfy $\psi(\psi+r)A(\psi)=0$. The roots of $A$ have negative real part exactly when $a_0>0$ and, if $a_2>0$, also $a_1>0$; nonnegative coefficients alone do not suffice ($a_2=a_0=1$, $a_1=0$ gives $\psi=\pm i$). This condition holds for all six laws listed with the model (elastic, viscous, Kelvin–Voigt, Maxwell, standard linear solid, Jeffrey), so for each of them the steady state $(1,\rho_0,0)$ is stable to spatially homogeneous perturbations. This corrects §4.1 as printed, which says "Since r is positive and the parameters $a_0$, $a_1$ and $a_2$ are all non-negative, the solution $\psi$ of such an algebraic equation is necessarily negative" and concludes stability "for any choice of the parameter $a_0$, $a_1$, $a_2$, $b_0$, $b_1$ and $b_2$": for $a_2=a_0=1$, $a_1=0$ the factor $\psi^2+1$ has the roots $\pm i$.

**Inhomogeneous perturbations.** For $k\ne0$ put

$$E_k=Dk^2+r,\qquad Q_k=\rho_0\bigl(s-\tau\lambda_1k^2+\tau\lambda_1\beta k^4\bigr),\qquad M_1=Q_k-\tau\lambda_2\rho_0k^2,\qquad M_0=Q_kE_k-\tau\lambda_2\alpha\rho_0^2k^4.$$

Perturbations proportional to $e^{\psi t+ikx}$ with $\psi\ne0$ exist exactly when

$$k^2B(\psi)\,(\psi+E_k)+A(\psi)\,(M_1\psi+M_0)=c_3\psi^3+c_2\psi^2+c_1\psi+c_0=0,$$

with

$$c_3=b_2k^2+a_2M_1,\qquad c_2=(b_2E_k+b_1)k^2+a_1M_1+a_2M_0,$$

$$c_1=(b_1E_k+b_0)k^2+a_0M_1+a_1M_0,\qquad c_0=b_0E_kk^2+a_0M_0 .$$

This corrects the coefficients (19)–(22) as printed, which agree with these only at $\rho_0=1$: the source prints, for example, $c_3(k^2)=a_2\tau\lambda_1\beta k^4+[b_2-a_2\tau(\lambda_1+\lambda_2\rho_0)]k^2+a_2s\rho_0$, whereas $b_2k^2+a_2M_1=a_2\tau\lambda_1\beta\rho_0k^4+[b_2-a_2\tau\rho_0(\lambda_1+\lambda_2)]k^2+a_2s\rho_0$, because the linearised ECM equation gives $\tilde\rho=-ik\rho_0\tilde u$ (Expansion), so every traction term in $\lambda_1$ carries the factor $\rho_0$, and the haptotactic term $\tau\lambda_2\alpha$ the factor $\rho_0^2$ (it appears as $a_2\tau\lambda_2\rho_0\alpha$ in the printed (20)). The difference matters: in the purely viscous case with $k=\eta=s=\lambda=1$, $\rho_0=2$, $\tau=6$, $\beta=1/2$, the coefficients above give $\psi^2+(D+r-1)\psi-(D+r)=(\psi-1)(\psi+D+r)$, so the displacement mode grows at rate $1$, while the printed (19)–(22) give $\psi^2+(D+r+\tfrac12)\psi+\tfrac12(D+r)$, whose roots are both negative.

Patterns require $\operatorname{Re}\psi>0$ for some root at some $k^2>0$. When $c_3>0$, all three roots have negative real part exactly when

$$c_2>0,\qquad c_0>0,\qquad c_2c_1>c_3c_0,$$

so the mode $k$ is unstable when one of these fails with a root of positive real part (a root on the imaginary axis is the borderline case). The signs of the coefficients alone do not decide stability: for the Jeffrey law with $E=\eta_1=\eta_2=D=r=\rho_0=1$, $\lambda=0$, $\tau=2$, $\beta=1/2$, $\alpha=1/8$, $s=3/2$, all four coefficients are nonnegative for every $k$, yet at $k=1$ the cubic is $\psi^3+\tfrac12\psi+\tfrac32=(\psi+1)(\psi^2-\psi+\tfrac32)$, whose two complex roots $\tfrac12\pm i\sqrt5/2$ have positive real part. This corrects §4.1 as printed, which says that "a necessary condition for this to happen is that at least one amongst $c_0(k^2)$, $c_1(k^2)$, $c_2(k^2)$ and $c_3(k^2)$ is negative for some $k^2>0$"; here $c_2(k^2)=3(k^2-1)^2\ge0$ and the other three coefficients are positive. In the degenerate cases:

- if $c_2=c_3=0$ (for instance the elastic law, $a_1=a_2=b_1=b_2=0$), then $\psi(k^2)=-c_0(k^2)/c_1(k^2)$, which is positive exactly when $c_0$ and $c_1$ have opposite signs;
- if only $c_3=0$ and $c_2>0$, some root has positive real part exactly when $c_1<0$ or $c_0<0$ (with all signs reversed when $c_2<0$).

**Traction is necessary.** At $\tau=0$ the polynomial factors as $(\psi+E_k)\bigl[k^2B(\psi)+\rho_0sA(\psi)\bigr]$. The first root is negative, and the quadratic factor has nonnegative coefficients and is not identically zero, so none of its roots has positive real part. Hence **positive cell traction $\tau>0$ is necessary for pattern formation**.

## Depends on

- [Cell–ECM mechanical model with a linear viscoelastic constitutive law](cell-ecm-mechanical-model-with-viscoelastic-matrix.md)

## Proof depends on

- [Cell–ECM mechanical model with a linear viscoelastic constitutive law](cell-ecm-mechanical-model-with-viscoelastic-matrix.md)
- [Routh–Hurwitz criterion for cubic polynomials](../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

At $n=1$ the traction factor $n/(1+\lambda n^2)$ has value $\lambda_1$ and derivative $\lambda_2$, which is where these constants enter. For $\psi\ne0$ the linearised ECM transport equation gives $\tilde\rho=-ik\rho_0\tilde u$, and the linearised cell equation gives $(\psi+E_k)\tilde n=-ik(\alpha\rho_0k^2+\psi)\tilde u$. Substituting both into the linearised force balance $-k^2B(\psi)\tilde u=A(\psi)\bigl[s\rho_0\tilde u-ik\bigl(\tau\lambda_2\rho_0\tilde n+\tau\lambda_1(1-\beta k^2)\tilde\rho\bigr)\bigr]$ and multiplying by $\psi+E_k$ gives the displayed cubic. Dividing by $c_3>0$, the Routh–Hurwitz criterion for monic cubics gives the stated stability conditions. For a quadratic with nonnegative coefficients the roots have nonpositive real part: real roots of such a quadratic are nonpositive, and complex roots have real part $-b/(2a)\le0$.

## Sources

- C. Villa, M. A. J. Chaplain, A. Gerisch, T. Lorenzi, *Mechanical models of pattern and form in biological tissues: the role of stress–strain constitutive equations*, Bulletin of Mathematical Biology 83 (2021), <https://doi.org/10.1007/s11538-021-00912-5> (PMCID: PMC8154836). Section 4.1, equations (18)–(24) and the stability argument for spatially homogeneous perturbations; the model equations (10)–(17) from which the coefficients are derived.
