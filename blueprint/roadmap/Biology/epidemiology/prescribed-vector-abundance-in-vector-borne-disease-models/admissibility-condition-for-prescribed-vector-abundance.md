# Admissibility condition for an externally prescribed vector abundance

**Setting.** Let $V(t)$, $t\in[t_0,T]$, be a prescribed total vector abundance and split it as $V=V_S+V_I$ into susceptible and infectious vectors. With host state $\mathbf H=(H_S,\mathbf H_I,\mathbf H_R)\in\mathbb R_+\times\mathbb R_+^n\times\mathbb R_+^m$ (susceptible, infectious and other host compartments), consider

$$
\begin{aligned}
\mathbf H'(t)&=\mathbf F_{\mathbf H}\bigl(t,\mathbf H(t),V_S(t),V_I(t)\bigr),\\
V_S'(t)&=V'(t)-V_I'(t),\\
V_I'(t)&=\lambda_{HV}\bigl(\mathbf H_I(t)\bigr)\bigl(V(t)-V_I(t)\bigr)+r(t)\,V_I(t),
\end{aligned}
$$

where $\lambda_{HV}$ is the force of infection from hosts to vectors and $r(t)$ the net per-capita change rate of infectious vectors other than new infections (for example $r=-\mu$ with vector mortality $\mu$ and no vertical transmission).

**Assumptions.** (A1) $V\in C^1([t_0,T])$ and $V\ge0$; (A2) $\mathbf F_{\mathbf H}$ is continuous in $t$ and locally Lipschitz in its other arguments; (A3) $\lambda_{HV}$ is locally Lipschitz; (A4) $r$ is continuous; (A5) $\lambda_{HV}(\mathbf H_I)\ge0$ for admissible $\mathbf H_I$; (A6) $V'(t)-r(t)V(t)\ge0$ for all $t\in[t_0,T]$.

**Proposition (well-posedness and admissibility).** Under (A1)–(A4) the system has a unique maximal solution for every initial condition with $\mathbf H(t_0)\ge0$, $0\le V_I(t_0)\le V(t_0)$ and $V_S(t_0)=V(t_0)-V_I(t_0)$, so $V_S+V_I=V$ for all times. Under (A1)–(A6) the solution is biologically admissible:

$$
0\le V_I(t)\le V(t)\qquad\text{for all }t \text{ in its interval of existence}.
$$

Condition (A6) is also necessary at the boundary $V_I=V$: there $V_S'=V'-rV$, so a prescribed abundance that declines faster than vector mortality allows ($V'+\mu V<0$ when $r=-\mu$) forces $V_S<0$. Trajectories violating (A6) must be regularized before use.

**Local reproduction index.** Freezing $V$, $r$ and $\mathbf F_{\mathbf H}$ at $t_0$ gives an autonomous system whose next-generation reproduction number $\mathcal R_l(t_0)$ characterizes extinction or emergence just after introduction; for strictly alternating host–vector transmission $\mathcal R_l(t_0)=\sqrt{\mathcal R_{l,VH}(t_0)\,\mathcal R_{l,HV}(t_0)}$. Since the full system is non-autonomous, $\mathcal R_l(t_0)<1$ gives local extinction in the frozen environment, while $\mathcal R_l(t_0)>1$ alone does not guarantee epidemic growth.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Existence and uniqueness are Cauchy–Lipschitz. For admissibility, $V_I$ solves a linear equation $V_I'=-(\lambda_{HV}-r)V_I+\lambda_{HV}V$ with nonnegative source when (A5) holds, so $V_I\ge0$ is preserved. The complement $W=V-V_I=V_S$ satisfies $W'=V'-\lambda_{HV}W-rV_I=-(\lambda_{HV}-r)W+(V'-rV)$, again linear in $W$ with a source that is nonnegative exactly under (A6), so $W\ge0$, i.e. $V_I\le V$, is preserved. In the Aedes–human arbovirus application this means that fitted adult mosquito abundance curves must satisfy $V'+\mu(T)V\ge0$ with temperature-dependent mortality $\mu$, which the source enforces by a regularization procedure.

## Sources

- L. Isnel, J. Papaïx, O. Bonnefon, S. Soubeyrand and L. Roques, "When vector abundance constrains vector-borne transmission: inside epidemic dynamics within a prescribed vector abundance", arXiv:2610.25971 (2026), Section 3 (general constrained system, assumptions (A1)–(A6), local reproduction index, Eq. for $\mathcal R_l$) and supplementary section on admissibility conditions for the infectious-vector compartment, <https://doi.org/10.48550/arXiv.2610.25971>.
