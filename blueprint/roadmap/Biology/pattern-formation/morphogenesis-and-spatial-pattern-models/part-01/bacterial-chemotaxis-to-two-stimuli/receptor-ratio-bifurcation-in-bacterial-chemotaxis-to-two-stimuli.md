# Receptor-ratio bifurcation in bacterial chemotaxis to two stimuli

**Model.** *E. coli* cells run at speed $\nu$ and tumble at rate $\lambda(a)=\lambda_0+ra^H$, which depends on the kinase activity $a$ of their mixed receptor clusters. Clusters of $N$ receptors contain Tar (sensing MeAsp, concentration $S_1$) and Tsr (sensing serine, concentration $S_2$) in ratio $\gamma=\text{Tar}/\text{Tsr}$; a heterogeneous MWC model gives activity relaxing (through methylation adaptation with speed $p$) towards an adapted level $q$, driven by the weighted log-sensing signal

$$
\frac{\gamma}{1+\gamma}\,\frac{\nabla S_1}{S_1}+\frac{1}{1+\gamma}\,\frac{\nabla S_2}{S_2}.
$$

The population density of run-and-tumble cells with internal state is described by a velocity-jump transport equation.

**Proposition (advection–diffusion limit, 1D).** If the densities decay exponentially in the internal variable and the gradients are shallow,

$$
\Big|\frac{\gamma}{1+\gamma}\frac{S_1'(x)}{S_1(x)}+\frac{1}{1+\gamma}\frac{S_2'(x)}{S_2(x)}\Big|\le\min\{q,1-q\}\,\frac{p}{\nu}\qquad(x\in[0,L]),
$$

then the cell density $n(x,t)$ is approximated by

$$
\partial_tn=\partial_x\Big(D\,\partial_xn-\chi\Big(\frac{\gamma}{1+\gamma}\frac{S_1'}{S_1}+\frac1{1+\gamma}\frac{S_2'}{S_2}\Big)n\Big),\qquad
D=\frac{\nu^2}{\lambda_0+rq^H},\quad \chi=\frac{rNHq^H(q-1)\nu^2}{(\lambda_0+rq^H)\big(Npq(q-1)-\lambda_0-rq^H\big)} .
$$

With Robin (no-flux) boundary conditions it has a unique, uniformly bounded solution.

**Lemma (receptor-ratio threshold).** Let $S_1$ be increasing and $S_2$ decreasing on $[0,L]$, write the drift as $V(x,\gamma)$, assume $\partial V/\partial x\le0$, and let cells start at $x_0$. Then there is $\gamma^*>0$ with $V(x_0,\gamma^*)=0$ such that cells accumulate to the right of $x_0$ (towards MeAsp) if $\gamma>\gamma^*$ and to the left (towards serine) if $\gamma<\gamma^*$. Explicitly $\gamma^*(x_0)=-\frac{S_2'/S_2}{S_1'/S_1}(x_0)$, the ratio of the two relative gradients. The proof of the source's Lemma 2 prints $\gamma(x)=(S_2'/S_2)/(S_1'/S_1)$ without the minus sign; $\gamma^*=-(S_2'/S_2)/(S_1'/S_1)(x_0)$ follows from $V(x_0,\gamma^*)=0$ with its (17), and is positive because $S_1'>0>S_2'$.

## Expansion

Because Tar and Tsr signals are integrated by the same cluster before driving the motor, the population responds to a single effective gradient, a $\gamma$-weighted average of the two log-gradients. Its sign decides the direction of drift, so even when one attractant has the larger concentration and the steeper (relative) gradient, cells with a small Tar/Tsr ratio go up the other gradient. The threshold is a bifurcation in the receptor ratio, consistent with experiments in which cells switch preference between serine and MeAsp as their Tar/Tsr ratio changes during growth. The 2D analogue, derived by moment closure under the same shallow-gradient condition, yields an advection–diffusion equation with drift along the corresponding weighted gradient, and agent-based simulations confirm the predicted switch.

## Sources

- Jeungeun Park, Zahra Aminzare, "A Mathematical Description of Bacterial Chemotaxis in Response to Two Stimuli", arXiv:2006.00688 (2020), Section 2 (microscopic model), Section 3 (Proposition 1, Lemmas 1–2), Section 4 (Remark 4), Section 5 (Assumptions 1–3, Lemmas 3–5), <https://doi.org/10.48550/arXiv.2006.00688>.
