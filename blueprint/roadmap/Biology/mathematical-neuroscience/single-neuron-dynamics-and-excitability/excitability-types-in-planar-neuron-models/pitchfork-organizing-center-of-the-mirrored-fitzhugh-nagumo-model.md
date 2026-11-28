# Pitchfork organizing center of the mirrored FitzHugh–Nagumo model

**Model.** The *mirrored FitzHugh–Nagumo model* replaces the linear recovery term of the FitzHugh–Nagumo model by a quadratic one:

$$\dot V=V-\frac{V^3}{3}-n^2+I_{\mathrm{app}},\qquad \dot n=\epsilon\big(n_\infty(V-V_0)+n_0-n\big),\qquad n_\infty(V)=\frac{2}{1+e^{-5V}},$$

with small $\epsilon>0$. The $V$-nullcline is the classical inverted N-shape together with its mirror image across the $V$-axis. The upper branch is *competitive*, $\frac{\partial\dot V}{\partial n}\frac{\partial\dot n}{\partial V}<0$, as in Hodgkin–Huxley sodium/potassium dynamics. The lower branch is *cooperative*, $\frac{\partial\dot V}{\partial n}\frac{\partial\dot n}{\partial V}>0$, modelling regenerative gating such as calcium-channel activation. At $I_{\mathrm{app}}=I^\star=2/3$ the two branches cross in a transcritical singularity at $(V,n)=(-1,0)$.

**Theorem.**

1. Fix $I_{\mathrm{app}}=I^\star$ and $n_0=n_0^\star(V_0)=-n_\infty(-1-V_0)$, and choose $V_0=V_0^\star=-1+\frac15\ln(4+\sqrt{15})\approx-0.587$ so that the $n$-nullcline is tangent to the $V$-nullcline at the singularity, i.e. $n_\infty'(-1-V_0)=1$ (with $y=e^{5(1+V_0)}$ this reads $10y/(1+y)^2=1$, i.e. $y^2-8y+1=0$). This gives a codimension-three degenerate (pitchfork) bifurcation. An affine change of coordinates brings the model to the local normal form

$$\dot v=\frac{v^2(3-v)}3-\big(k(V_0)(v-u)+\delta_0\big)^2+I_{\mathrm{app}}-I^\star,\qquad \dot u=-\epsilon u+O(v^2,vu,u^2),$$

with $k(V_0)=n_\infty'(-1-V_0)$.
2. For small $\epsilon$ and near the singular value $I^\star+I_c(\sqrt\epsilon)$, the singularly perturbed transcritical point exchanges the attracting and repelling slow manifolds, as in the canard theory of Krupa and Szmolyan.
3. Unfolding the organizing center in $(V_0,n_0)$ divides parameter space into five regions with different responses to a ramp of $I_{\mathrm{app}}$. In the competitive regions these are Type I (saddle-node on invariant circle), Type II (Hopf) and Type III excitability. In the cooperative regions, where the resting state lies on the mirrored branch, there are two further types. *Type IV* is a saddle-node at $I_{SN}$ together with a singularly perturbed saddle-homoclinic bifurcation at $I_{SH}<I_{SN}$, giving bistability between rest and spiking. *Type V* (saddle–saddle) has coexisting down- and up-states separated by a saddle, with a Hopf bifurcation of the up-state.

## Proof sketch

In the classical model the slow variable always opposes the fast one, and only Types I–III can occur. Making the recovery term quadratic lets the same slow variable act regeneratively at hyperpolarized potentials, which is the geometric signature of calcium activation found in planar reductions of conductance-based models. The pitchfork, the point where the transcritical singularity of the fast nullcline meets a tangency with the slow nullcline, organizes all five behaviours in one chart. Moving away from it in the two geometric parameters selects which bifurcation sequence a current ramp encounters. Types IV and V reproduce plateau potentials, bistability between rest and repetitive firing, and switching between tonic and burst-like firing. These are observed experimentally in neurons with strong calcium currents, and competitive models cannot produce them.

## Sources

- Alessio Franci, Guillaume Drion and Rodolphe Sepulchre, "An Organizing Center in a Planar Model of Neuronal Excitability", *SIAM Journal on Applied Dynamical Systems* 11 (2012), 1698–1722, <https://doi.org/10.1137/120875016>. Preprint version: arXiv:1204.5686 (2012), Section 2 (mirrored FitzHugh–Nagumo model), Section 3 (codimension-three construction and Lemma 1 normal form, Theorem 1 adapted from Krupa–Szmolyan), Section 4 (Types I–III), Section 5 (Types IV and V), appendix (singularly perturbed global phase portraits), <https://doi.org/10.48550/arXiv.1204.5686>.
