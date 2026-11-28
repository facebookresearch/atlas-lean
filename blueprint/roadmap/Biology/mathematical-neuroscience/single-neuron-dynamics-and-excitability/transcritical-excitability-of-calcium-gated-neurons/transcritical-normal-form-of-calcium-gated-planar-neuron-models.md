# Transcritical normal form of calcium-gated planar neuron models

**Setting.** Reduce the Hodgkin–Huxley model, augmented by a slow non-inactivating calcium current and a hyperpolarizing pump current, to a planar fast–slow system for the membrane potential $V$ and an aggregate recovery variable $n$:

$$
\dot V=f_V(V,n,I_{\mathrm{app}}),\qquad \dot n=\epsilon\,g(V,n),
$$

with $f_V$ affine in the applied current, $\partial f_V/\partial I_{\mathrm{app}}=1$. With strong calcium conductance, $n$ acts as an excitatory variable for small $n$ (calcium activation) and an inhibitory one for large $n$, so the total ionic current is non-monotone in $n$ and the voltage nullcline $\{f_V=0\}$ has two branches ("hourglass" shape) that cross at a critical current $I_{tc}$.

**Transversal self-intersection.** At $I_{\mathrm{app}}=I_{tc}$ there is a point $(V_{tc},n_{tc})$ with

$$
f_V=0,\qquad \partial_Vf_V=0,\qquad \partial_nf_V=0,\qquad
\det\begin{pmatrix}\partial^2_{VV}f_V&\partial^2_{Vn}f_V\\ \partial^2_{Vn}f_V&\partial^2_{nn}f_V\end{pmatrix}<0,\qquad \partial^2_{VV}f_V\ne0 .
$$

In the singular limit $\epsilon=0$, this is a **transcritical bifurcation** of the fast voltage dynamics with $n$ as parameter: for $n\ne n_{tc}$ there are two voltage equilibria (left stable, right unstable) that exchange stability through the crossing.

**Lemma (Franci–Drion–Seutin–Sepulchre, supplementary Section S.1, Lemma 1).** Let $g_0=g(V_{tc},n_{tc})<0$ (the recovery nullcline lies below the crossing). With $\alpha=\tfrac12\partial^2_{VV}f_V$, $\beta=\tfrac12\partial^2_{Vn}f_V$, $\gamma=\tfrac12\partial^2_{nn}f_V$ at the crossing, the affine change of coordinates $v=\alpha(V-V_{tc})+\beta(n-n_{tc})$, $w=\sqrt{\beta^2-\gamma\alpha}\,(n-n_{tc})$ and rescalings of $\epsilon$ and of the input transform the system into

$$
\dot v=v^2-w^2+I+h_1(v,w,\epsilon),\qquad \dot w=\epsilon\big(-1+h_2(v,w,\epsilon)\big),
$$

with $h_1=O(v^3,v^2w,vw^2,w^3,\epsilon v,\epsilon w,\epsilon^2)$, $h_2=O(v,w,\epsilon)$ and rescaled input $I=\lambda\epsilon+\alpha(I_{\mathrm{app}}-I_{tc})$, $\lambda=-\beta/\sqrt{\beta^2-\gamma\alpha}$. For $I=0$ the two nullcline branches are $w=\pm v$.

This replaces the fold normal form $\dot v=v^2-w+I$ underlying the classical (FitzHugh) picture of excitability: the transcritical point is present but non-physiological in the classical reduced Hodgkin–Huxley phase portrait, and calcium channels bring it into the physiological range.

## Proof sketch

Since $\partial_Vf_V$ and $\partial_nf_V$ do not depend on the input, the extrema of the two branches lie on the fixed curves $\partial_Vf_V=0$ and $\partial_nf_V=0$, and they coincide at the crossing, giving the first three conditions; the sign conditions are generic and checked numerically. The negative Hessian determinant makes the quadratic part of $f_V$ an indefinite form, which the affine change brings to $v^2-w^2$; the slow drift $g_0<0$ becomes $\dot w=-\epsilon$ after rescaling.

## Sources

- Guillaume Drion, Alessio Franci, Vincent Seutin and Rodolphe Sepulchre, "A Novel Phase Portrait for Neuronal Excitability", *PLoS ONE* 7 (2012), e41806, <https://doi.org/10.1371/journal.pone.0041806>. Preprint version: arXiv:1112.2588 (2011), main text Sections 2–4 and supplementary Section S.1, <https://doi.org/10.48550/arXiv.1112.2588>.
