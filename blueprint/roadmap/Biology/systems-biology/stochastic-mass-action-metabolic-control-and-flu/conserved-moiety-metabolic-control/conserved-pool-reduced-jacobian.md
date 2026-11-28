# Reduced Jacobian of a conserved-pool network

The reduced Jacobian is the Jacobian of the steady-state equations in reduced coordinates, $N_R\varepsilon'B$; its invertibility is the regularity condition that survives when conserved pools make the full Jacobian singular.

Let $M,R$ be finite, $N\in\mathbb{R}^{M\times R}$ of rank $q$, and let $(B,L)$ with $N=BN_R$ be a [conserved-pool presentation](conserved-pool-reduced-coordinates.md). Let $f_i\colon\mathbb{R}^M\to\mathbb{R}$, $i\in R$, be rate laws with [fluxes](../flux.md) $v_i(e,s)=e_if_i(s)$, and let $e\in\mathbb{R}^R$ and $s\in\mathbb{R}^M$ be such that every $f_i$ is differentiable at $s$. The **unscaled elasticity matrix** is

$$\varepsilon'(e,s)\in\mathbb{R}^{R\times M},\qquad \varepsilon'_{im}=\frac{\partial v_i}{\partial s_m}(e,s)=e_i\,\frac{\partial f_i}{\partial s_m}(s),$$

and the **reduced Jacobian** is the square matrix

$$J_{\mathrm{red}}(e,s)=N_R\,\varepsilon'(e,s)\,B\in\mathbb{R}^{q\times q}.$$

The following hold.

1. **Choice independence.** For another presentation with $B'=BP$, $N_R'=P^{-1}N_R$, the reduced Jacobian is $P^{-1}J_{\mathrm{red}}P$; invertibility, determinant and eigenvalues do not depend on the choice.
2. **Equivalent regularity conditions.** The following are equivalent: (a) $J_{\mathrm{red}}(e,s)$ is invertible; (b) the restriction of $N\varepsilon'(e,s)$ to $\operatorname{im}N$ is a bijection $\operatorname{im}N\to\operatorname{im}N$; (c) the stacked matrix with blocks $N\varepsilon'(e,s)$ above $L$, of size $(|M|+p)\times|M|$, has rank $|M|$.
3. **A necessary rank condition.** If $J_{\mathrm{red}}(e,s)$ is invertible then $\operatorname{rank}(N\varepsilon'(e,s))=\operatorname{rank}N$. The converse fails: for $M=\{1,2\}$, one reaction with $N=(1,-1)^{\mathsf T}$ and $\varepsilon'=(1\ \ 1)$, both ranks are $1$ but $J_{\mathrm{red}}=0$ for $B=N$.

## Depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)
- [Reaction fluxes proportional to enzyme levels](../flux.md)

## Proof depends on

- [Reduced coordinates for conserved pools](conserved-pool-reduced-coordinates.md)

## Expansion

Item 1 is the computation $P^{-1}N_R\varepsilon'BP$. For item 2 write $A=N\varepsilon'=BN_R\varepsilon'$, so $A$ maps $\mathbb{R}^M$ into $\operatorname{im}B$, and $A(Bw)=B\,J_{\mathrm{red}}w$; since $B$ is an isomorphism $\mathbb{R}^q\to\operatorname{im}N$, the restriction in (b) is conjugate to $J_{\mathrm{red}}$, giving (a)$\Leftrightarrow$(b). The kernel of the stacked matrix is $\{\delta:A\delta=0,\ L\delta=0\}$; as $\ker L=\operatorname{im}B$, it equals $B\ker J_{\mathrm{red}}$, giving (a)$\Leftrightarrow$(c). For item 3, invertibility makes $A$ surjective onto $\operatorname{im}N$, so its rank is $q$; the counterexample has $A=\begin{pmatrix}1&1\\-1&-1\end{pmatrix}$, whose kernel is exactly $\operatorname{im}N$.

Smallbone et al. observe that formulas built on the stoichiometric link matrix require $\operatorname{rank}(N\varepsilon')=\operatorname{rank}N$; item 3 shows that their rank condition is necessary for invertibility of the reduced Jacobian but not sufficient, so the invertibility of $J_{\mathrm{red}}$ is assumed separately wherever it is used.

The [reduced homeostasis matrix criterion](../../regulatory-and-signalling-circuits/infinitesimal-homeostasis-in-mass-action-systems/reduced-homeostasis-matrix-criterion.md) uses “reduced Jacobian” for a different, full-size matrix combining conservation rows and independent dynamical rows. Its nonsingularity is related to the stacked full-column-rank condition in item 2(c), not to equality of the two matrices.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (6) and (7) (unscaled elasticity matrix and the reduced matrix $N_r\varepsilon'L$), and the Results subsection “Control analysis” on the rank condition for Reder's formula.
