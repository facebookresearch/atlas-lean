# Castillo-Chavez–Song centre-manifold bifurcation theorem

**Setting.** Consider a parametrized system

$$\frac{dx}{dt} = f(x, \phi), \qquad x \in \mathbb{R}^n,\ \phi \in \mathbb{R},$$

with $f$ of class $C^2$ on $\mathbb{R}^n \times \mathbb{R}$ and $f(0, \phi) = 0$ for all $\phi$, so $x = 0$ is
an equilibrium for every parameter value (in epidemic models: the disease-free equilibrium after
translation, with $\phi = \beta - \beta^*$ the deviation of a transmission rate from its value
$\beta^*$ at $\mathcal{R}_0 = 1$). Assume:

- **(A1)** $A = D_x f(0, 0)$ has $0$ as a simple eigenvalue and all other eigenvalues of $A$ have negative
  real parts;
- **(A2)** $A$ has a nonnegative right eigenvector $w$ and a left eigenvector $v$ for the eigenvalue $0$,
  normalized by $v \cdot w = 1$.

Let $f_k$ be the $k$-th component of $f$ and define the bifurcation coefficients

$$a = \sum_{k,i,j=1}^{n} v_k w_i w_j \frac{\partial^2 f_k}{\partial x_i \partial x_j}(0, 0), \qquad
b = \sum_{k,i=1}^{n} v_k w_i \frac{\partial^2 f_k}{\partial x_i \partial \phi}(0, 0).$$

**Theorem.** Suppose $a \ne 0$ and $b \ne 0$. For $|\phi|$ sufficiently small, the equilibria near $x = 0$ are
$0$ and one further equilibrium $x^*(\phi) = c^*(\phi)\, w + o(|\phi|)$ with
$c^*(\phi) = -2b\phi/a + o(|\phi|)$, called positive or negative according to the sign of $c^*$, and:

1. $a > 0$, $b > 0$: for $\phi < 0$, $0$ is locally asymptotically stable and there is a positive unstable
   equilibrium; for $\phi > 0$, $0$ is unstable and there is a negative, locally asymptotically stable
   equilibrium;
2. $a < 0$, $b < 0$: for $\phi < 0$, $0$ is unstable and there is a positive, locally asymptotically stable
   equilibrium; for $\phi > 0$, $0$ is locally asymptotically stable and there is a negative unstable
   equilibrium;
3. $a > 0$, $b < 0$: for $\phi < 0$, $0$ is unstable and there is a negative, locally asymptotically stable
   equilibrium; for $\phi > 0$, $0$ is locally asymptotically stable and there is a positive unstable
   equilibrium;
4. $a < 0$, $b > 0$: for $\phi < 0$, $0$ is locally asymptotically stable and there is a negative unstable
   equilibrium; for $\phi > 0$, $0$ is unstable and there is a positive, locally asymptotically stable
   equilibrium.

**Epidemiological reading.** Take $b > 0$, the usual case when $\phi$ raises transmission. If $a < 0$
(case 4) the bifurcation at $\mathcal{R}_0 = 1$ is forward: a positive, locally asymptotically stable
endemic equilibrium appears for $\mathcal{R}_0$ slightly above $1$, and none exists nearby for
$\mathcal{R}_0$ slightly below $1$. If $a > 0$ (case 1) it is backward: for $\mathcal{R}_0$ slightly below $1$ a
positive unstable endemic equilibrium coexists with the locally asymptotically stable disease-free
equilibrium, which is therefore not globally asymptotically stable on the feasible region. The theorem
is local and does not by itself give a further, stable endemic equilibrium; such bistability needs a
separate existence and stability argument in a specific model.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

By (A1) the flow near $(0, 0)$ reduces to a one-dimensional centre manifold tangent to $w$. Writing
$x = c\, w + O(c^2 + |c\phi|)$ and projecting onto $v$ (using $v \cdot w = 1$) gives the normal form

$$\dot c = \tfrac{1}{2} a\, c^2 + b\, \phi\, c + O\bigl(|c|^3 + \phi^2 |c| + |\phi| c^2\bigr).$$

The origin has linearization $b\phi$, and the nontrivial equilibrium $c^* \approx -2 b \phi / a$ has
linearization $a c^* + b\phi \approx -b\phi$. So $0$ is stable exactly when $b\phi < 0$, the other branch is
stable exactly when $b\phi > 0$, and the branch has the sign of $-b\phi/a$; these three signs give the
four cases. For example, $x' = -x^2 - \phi x$ has $a = -2$, $b = -1$ and other equilibrium $-\phi$, which is
negative and unstable for $\phi > 0$, as in case 2.

**Discrepancy in the source.** Item ii of Theorem 4.1 as printed says that, for $a < 0$, $b < 0$ and
$0 < \phi \ll 1$, there is a *positive* unstable equilibrium. The same paper's normal form (its equation
(31)) and its summary Table 3 give the sign stated in case 2 above, as does the scalar example. The
paper also remarks that nonnegativity of $w$ can be relaxed in the coordinates where the equilibrium is
positive (for example susceptible classes); positivity of the bifurcating branch then refers to the
infected coordinates.

In epidemic models the left eigenvector $v$ has zero entries in the uninfected compartments, so $a$
collects only second derivatives of the infected equations; disease-induced mortality, imperfect
vaccination, reinfection, treatment returning individuals to susceptibility, environmental reservoirs or
incident co-infection can make $a$ positive. Applications:

- In the malaria sub-model of a malaria–COVID-19 system, with the mosquito-to-human transmission rate
  as bifurcation parameter, $b = v_2 w_6 b_{\mathrm{bite}} > 0$ and the explicit sign condition $a > 0$
  (Tchoumi et al., Eq. (24)) yields a backward bifurcation, whereas the COVID-19 sub-model has $a < 0$
  and only a forward bifurcation.
- A SARS-CoV-2–Zika co-infection model (Omame et al.), a COVID-19 mitigation model (Kassa et al.,
  Theorem 3.3) and the pneumonia sub-model of an HIV/AIDS–pneumonia model (Teklu and Rao,
  Theorem 5) compute $a > 0$, $b > 0$ in parameter regions and so have a backward bifurcation there.
- In an SEICR COVID-19 model with a comorbid class (Das et al., Theorem 3) the computation gives
  $a < 0$, $b > 0$: the endemic equilibrium bifurcates forward and is locally asymptotically stable for
  $\mathcal{R}_0$ slightly above $1$.
- In a COVID-19 vaccination model with a leaky vaccine (Shen et al.), the imperfect vaccine produces
  $a > 0$; with a perfect vaccine a linear Lyapunov function shows that the disease-free equilibrium is
  globally asymptotically stable for $\mathcal{R} \le 1$, so no backward bifurcation occurs.

The equilibrium count in such models is often read off a quadratic, see
[Quadratic endemic-equilibrium condition for backward bifurcation](quadratic-endemic-equilibrium-condition-for-backward-bifurcation.md).
Under a backward bifurcation the
Castillo-Chavez–Feng–Huang global stability criterion
cannot apply for $\mathcal{R}_0$ slightly below $1$.

## Sources

- C. Castillo-Chavez, B. Song, "Dynamical models of tuberculosis and their applications",
  Mathematical Biosciences and Engineering 1 (2004) 361-404, Theorem 4.1, Eq. (31) and Table 3,
  <https://doi.org/10.3934/mbe.2004.1.361>.
- S. Y. Tchoumi, M. L. Diagne, H. Rwezaura, J. M. Tchuenche, "Malaria and COVID-19 co-dynamics: A
  mathematical model and optimal control", Applied Mathematical Modelling 99 (2021), Sections
  3.1-3.2, Eqs. (9)-(11) and (22)-(24), <https://doi.org/10.1016/j.apm.2021.06.016> (PMC8249695).
- A. Omame, M. Abbas, C. P. Onyenegecha, "Backward bifurcation and optimal control in a co-infection
  model for SARS-CoV-2 and ZIKV", Results in Physics 37 (2022) 105481, backward bifurcation analysis
  of model (11), <https://doi.org/10.1016/j.rinp.2022.105481> (PMC8994284).
- S. M. Kassa, J. B. H. Njagarah, Y. A. Terefe, "Analysis of the mitigation strategies for COVID-19:
  From mathematical modelling perspective", Chaos, Solitons and Fractals 138 (2020) 109968,
  Theorem 3.3 and Appendix B (bifurcation coefficients (32)–(33)),
  <https://doi.org/10.1016/j.chaos.2020.109968>.
- S. W. Teklu, K. P. Rao, "HIV/AIDS-Pneumonia Codynamics Model Analysis with Vaccination and
  Treatment", Computational and Mathematical Methods in Medicine 2022 (2022) 3105734, Theorem 5,
  <https://doi.org/10.1155/2022/3105734>.
- P. Das, R. K. Upadhyay, A. K. Misra, F. A. Rihan, P. Das, D. Ghosh, "Mathematical model of
  COVID-19 with comorbidity and controlling using non-pharmaceutical interventions and vaccination",
  Nonlinear Dynamics 106 (2021) 1213–1227, Theorem 3, <https://doi.org/10.1007/s11071-021-06517-w>
  (PMC8133070).
- Z.-H. Shen, Y.-M. Chu, M. A. Khan, S. Muhammad, O. A. Al-Hartomy, M. Higazy, "Mathematical
  modeling and optimal control of the COVID-19 dynamics", Results in Physics 31 (2021) 105028,
  vaccination model (Theorems 3–5), <https://doi.org/10.1016/j.rinp.2021.105028> (PMC8627298).
