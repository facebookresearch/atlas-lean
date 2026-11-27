# Structural identifiability of the layered cell-population model

In the layered cell-population model (cells divide and move irreversibly to the next layer), suppose the division rates are age independent, $b_j(a)=b_j>0$, that $p_S^{(j)}\in(0,1)$ for $j<J$ with $p_S^{(J)}=1$, and that the population starts with $N$ newborn cells in layer $1$. Integrating the age-structured equations over age, the mean cell numbers $M_j(t)$ per layer satisfy the linear system

$$ \frac{dM_1}{dt}=(2p_S^{(1)}-1)b_1M_1,\qquad \frac{dM_j}{dt}=(2p_S^{(j)}-1)b_jM_j+2(1-p_S^{(j-1)})b_{j-1}M_{j-1}\ \ (2\le j\le J),\qquad M(0)=(N,0,\dots,0). $$

**Theorem.** Under complete observation of $t\mapsto M(t)$, the parameter set $\{N,\ b_j,\ p_S^{(j)}\}$ is structurally identifiable: if two parameter sets produce the same trajectory $M(t)$ for all $t\ge0$, they coincide.

## Depends on

- [Malthus parameter of a unidirectional layered age-structured population](malthus-parameter-of-a-unidirectional-layered-age-structured-population.md)

## Expansion

Write the system as $M'=A_PM$ with $A_P$ lower bidiagonal. Equal trajectories give $(A_P-A_{\tilde P})M(t)=0$ for all $t$. The trajectory is not confined to any proper subspace: if $u^\top M(t)\equiv0$, evaluating at $t=0$ gives $u_1=0$, and repeated differentiation at $t=0$ gives successively $u_2=\dots=u_J=0$, because each off-diagonal entry $2p_L^{(j)}b_j$ is nonzero. Hence $A_P=A_{\tilde P}$, i.e. $(2p_S^{(j)}-1)b_j$ and $2p_L^{(j)}b_j$ are determined; their sum is $b_j$, which then determines $p_S^{(j)}$, and $N=M_1(0)$. The paper uses this to calibrate the model to cell counts per layer in early ovarian follicle development.

## Sources

- F. Clément, F. Robin and R. Yvinec, "Analysis and calibration of a linear model for structured cell populations with unidirectional motion: application to the morphogenesis of ovarian follicles", arXiv:1712.05372 (2017), <https://doi.org/10.48550/arXiv.1712.05372>. Theorem on identifiability of all layers and its preceding kernel lemma (subsection "Structural identifiability" of Section "Parameter calibration"), with the mean-number system obtained under the age-independent and first-layer-start hypotheses. Published version: SIAM Journal on Applied Mathematics 79 (2019) 207–229, <https://doi.org/10.1137/17m1161336>.
