# Parallel-line steady states of the anisotropic interaction model

**Model.** $N$ particles at positions $x_j(t)$ on the unit torus $\mathbb T^2$ move by

$$
\frac{dx_j}{dt}=\frac1N\sum_{k\ne j}F\big(x_j-x_k,T(x_j)\big),
$$

where $T(x)=\chi\,s(x)\otimes s(x)+l(x)\otimes l(x)$, $\chi\in[0,1]$, is a stress tensor field built from orthonormal vector fields $s$ (smallest stress) and $l$ (largest stress). Two force families are considered:
- *Kücken–Champod type*: $F(d,T)=f_R(|d|)\,d+f_A(|d|)\,T\,d$, with short-range repulsion $f_R(\rho)=(\alpha\rho^2+\beta)e^{-e_R\rho}$ and attraction $f_A(\rho)=-\gamma\rho e^{-e_A\rho}$, so that the force coefficient is $f_R+f_A$ along $l$ and $f_R+\chi f_A$ along $s$;
- *Directional type*: $F(d,T)=f_s(|d|)(s\cdot d)\,s+f_l(|d|)(l\cdot d)\,l$, with separate radial coefficients along $s$ and $l$ (for instance exponentially damped oscillatory profiles).

Forces have finite range on the torus, $F(x-x',T(x))=0$ for $|x-x'|\ge 1/2$. The model is the overdamped limit of Newtonian particles with friction, and for $\chi=1$ the Kücken–Champod force reduces to an isotropic gradient flow.

**Proposition.** Let $T$ be spatially homogeneous with $s=(0,1)$ and $l=(1,0)$. Let $d\in(0,1]$ with $n=1/d\in\mathbb N$ and let $N$ be a multiple of $n$. Then $n$ parallel equidistant vertical lines at spacing $d$, each carrying $N/n$ particles uniformly spaced along it, form a steady state for either force family.

Any other spatially homogeneous tensor field is reduced to this one by a rotation, and translates of steady states are steady states. Stripe patterns of this kind are the building blocks for simulating fingerprint ridges, where $l$ follows the observed ridge orientation field and the spacing is controlled by rescaling the force coefficients.

## Expansion

Both force families are odd in $d$, $F(-d,T)=-F(d,T)$ (Newton's third law). Take a particle on one line. The other particles on its own line come in pairs symmetric about it, whose forces cancel. When $N/n$ is even, the unpaired particle sits at distance exactly $1/2$ and contributes nothing because of the cutoff. The lines themselves come in symmetric pairs on the torus, except, for even $n$, the line at horizontal distance $1/2$, which is out of range. Every particle therefore feels zero net force. Whether such stripes are stable depends on how they are aligned with $s$, and that question is separate from this existence statement.

## Sources

- B. Düring, C. Gottschlich, S. Huckemann, L. M. Kreusser, "An Anisotropic Interaction Model for Simulating Fingerprints", arXiv:1711.07417 (2017), Section 1 (particle model and forces), Section 2 (Kücken–Champod and bio-inspired force coefficients, general setting), Section 3.1 (Proposition 3.1), <https://doi.org/10.48550/arXiv.1711.07417>.
