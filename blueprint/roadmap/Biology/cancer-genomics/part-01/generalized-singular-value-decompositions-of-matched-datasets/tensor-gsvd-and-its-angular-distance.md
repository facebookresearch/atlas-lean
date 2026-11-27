# Tensor GSVD and its angular distance

**Matrix GSVD.** Let $D_1 \in \mathbb R^{K_1 \times N}$ and $D_2 \in \mathbb R^{K_2 \times N}$ have full column rank and the same columns (e.g. patients). Their generalized singular value decomposition is

$$D_i = U_i \Sigma_i V^{\mathsf T}, \qquad i = 1, 2,$$

with $U_i^{\mathsf T} U_i = I$, $\Sigma_i = \mathrm{diag}(\sigma_{i,1}, \dots, \sigma_{i,N})$ positive, and $V$ invertible with normalized but in general non-orthogonal columns, shared by both datasets. The *GSVD angular distance* of the $a$-th pattern is

$$\theta_a = \arctan\!\left(\frac{\sigma_{1,a}}{\sigma_{2,a}}\right) - \frac{\pi}{4} \in \left[-\frac{\pi}{4}, \frac{\pi}{4}\right]. \tag{5}$$

Here $\theta_a = \pi/4$ (resp. $-\pi/4$) marks a pattern exclusive to $D_1$ (resp. $D_2$), and $\theta_a = 0$ one common to both.

**Tensor GSVD.** Let $\mathcal D_i \in \mathbb R^{K_i \times L \times M}$ ($i = 1,2$) be third-order tensors with matched column dimensions $L$ (patients) and $M$ (platforms) and independent row dimensions $K_i$ (probes). Take $U_i$ from the GSVD of the row-mode unfoldings $D_i \in \mathbb R^{K_i \times LM}$, and $V_x$, $V_y$ from the GSVDs of the unfoldings preserving the $L$- and the $M$-dimension. Contracting $\mathcal D_i$ with $U_i^{\mathsf T}$, $V_x^{-1}$ and $V_y^{-1}$ defines core tensors $\mathcal R_i$, giving

$$\mathcal D_i = \mathcal R_i \times_a U_i \times_b V_x \times_c V_y = \sum_{a,b,c} \mathcal R_{i,abc}\; u_{i,a} \otimes v_{x,b} \otimes v_{y,c}. \tag{1}$$

The tensor GSVD exists for tensors of any order and is unique up to signs and rotations within degenerate subspaces. For second-order tensors it reduces to the matrix GSVD, and when $D_1$ is the identity it reduces to the higher-order SVD of $\mathcal D_2$.

**Theorem.** With the tensor GSVD angular distance $\Theta_{abc} = \arctan(\mathcal R_{1,abc}/\mathcal R_{2,abc}) - \pi/4$,

$$\Theta_{abc} = \theta_a \qquad \text{for all } a, b, c .$$

In particular $\mathcal R_{1,abc}/\mathcal R_{2,abc} = \sigma_{1,a}/\sigma_{2,a} > 0$, so $|\Theta_{abc}| \le \pi/4$, although the core entries themselves need not be positive.

## Expansion

Unfolding (1) along the row mode gives $D_i = U_i R_i (V_x^{\mathsf T} \otimes V_y^{\mathsf T})$, where $R_i$ is the unfolded core and $\otimes$ is the Kronecker product. Comparing with $D_i = U_i \Sigma_i V^{\mathsf T}$ yields $R_i = \Sigma_i V^{\mathsf T}(V_x^{-\mathsf T} \otimes V_y^{-\mathsf T})$. Row $a$ of $R_1$ and of $R_2$ is the same row vector scaled by $\sigma_{1,a}$ and $\sigma_{2,a}$, so every entry ratio equals $\sigma_{1,a}/\sigma_{2,a}$. The same argument works for tensors of any order. The arctangent form is natural because the GSVD is related to the cosine–sine decomposition, $\sigma_{1,a}$ and $\sigma_{2,a}$ playing the roles of sine and cosine of an angle. Within each dataset, the significance of a subtensor is $\mathcal P_{i,abc} = \mathcal R_{i,abc}^2 / \sum \mathcal R_{i,a'b'c'}^2$. In ovarian serous cystadenocarcinoma, the most tumor-exclusive pattern of co-occurring copy-number alterations on certain chromosome arms, consistent across platforms, predicted survival independently of stage.

## Sources

- P. Sankaranarayanan, T. E. Schomay, K. A. Aiello, O. Alter, "Tensor GSVD of patient- and platform-matched tumor and normal DNA copy-number profiles uncovers chromosome arm-wide patterns of tumor-exclusive platform-consistent alterations encoding for cell transformation and predicting ovarian cancer survival", *PLoS ONE* (2015), Methods ("Construction", Eqs. (1)–(3); "Existence, uniqueness and special cases"; "Interpretation", Eqs. (4)–(6) and Theorem 1), <https://doi.org/10.1371/journal.pone.0121396> (PMC4398562).
