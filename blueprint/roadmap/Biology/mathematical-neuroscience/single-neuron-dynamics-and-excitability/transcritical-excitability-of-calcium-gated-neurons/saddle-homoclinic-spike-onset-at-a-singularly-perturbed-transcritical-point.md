# Saddle-homoclinic spike onset at a singularly perturbed transcritical point

**Setting.** Consider the transcritical fast–slow normal form

$$
\dot v=v^2-w^2+I+h_1(v,w,\epsilon),\qquad \dot w=\epsilon\big(-1+h_2(v,w,\epsilon)\big),
$$

obtained from calcium-gated planar neuron models. For $\epsilon=0$ the critical set $S_0=\{v^2-w^2+I+h_1=0\}$ has attracting branches $S_a^\pm$ and repelling branches $S_r^\pm$ above and below the transcritical singularity. For small $\epsilon>0$ Fenichel theory gives attracting and repelling slow invariant curves $S_a^\epsilon,S_r^\epsilon$ away from the singularity. Fix a section $\Delta=\{v_-\le v\le v_+,\ w=\rho\}$ with $\rho<0$ small, and let $q_{a,\epsilon},q_{r,\epsilon}$ be the intersections of $S_a^\epsilon,S_r^\epsilon$ with $\Delta$.

**Theorem (Franci–Drion–Seutin–Sepulchre, supplementary Section S.1, Theorem 1; adapted from Krupa–Szmolyan's analysis of transcritical points).** There are $\epsilon_0>0$ and a smooth function $I_c(\sqrt\epsilon)$ on $[0,\epsilon_0]$ with $I_c(0)=0$ such that for every $\epsilon\in(0,\epsilon_0]$:

1. $q_{a,\epsilon}=q_{r,\epsilon}$ if and only if $I=I_c(\sqrt\epsilon)$;
2. on an open interval of inputs containing $I_c(\sqrt\epsilon)$ both intersections exist and $\partial_I(q_{a,\epsilon}-q_{r,\epsilon})>0$.

Since $S_a^\epsilon$ and $S_r^\epsilon$ coincide with the unstable and stable separatrices of the saddle, this gives a **saddle-homoclinic bifurcation** at $I=I_c(\sqrt\epsilon)$: for $I<I_c$ the unstable separatrix returns to the stable resting node (a single spike, then rest), at $I=I_c$ it forms a homoclinic loop, and for $I>I_c$ it spirals onto an exponentially stable spiking limit cycle. The transition is organized by the saddle's separatrices, which explains spike latency, plateau oscillations and after-depolarization potentials in neurons with strong calcium currents.

**Transcritical hybrid model.** Following Izhikevich's hybrid approach, the spike downstroke is replaced by a reset:

$$
\dot v=v^2-w^2+I,\qquad \dot w=\epsilon(av-w+w_0),\qquad \text{if } v\ge v_{th}:\ v\leftarrow c,\ w\leftarrow d .
$$

The parameter $w_0$ mirrors calcium conductance: $w_0>0$ (recovery nullcline crossing the upper branch) recovers the classical fold-type excitability of the Izhikevich model, while $w_0<0$ (crossing the lower branch) gives the calcium-type phase portraits, and the model reproduces thalamocortical relay neuron firing patterns.

## Depends on

- [Transcritical normal form of calcium-gated planar neuron models](transcritical-normal-form-of-calcium-gated-planar-neuron-models.md)

## Proof sketch

Near the transcritical point the slow invariant curves cannot be continued by Fenichel theory alone; blow-up analysis shows that, depending on the sign of $I-I_c(\sqrt\epsilon)$, the attracting slow curve arriving from above passes to the left or right of the repelling one. The splitting $q_{a,\epsilon}-q_{r,\epsilon}$ is monotone in $I$, so it vanishes exactly once, at the homoclinic value. The fold normal form $v^2-w+I$ only captures the part of the phase portrait above the singularity; the transcritical form $v^2-w^2+I$ captures both nullcline branches.

## Sources

- Guillaume Drion, Alessio Franci, Vincent Seutin and Rodolphe Sepulchre, "A Novel Phase Portrait for Neuronal Excitability", *PLoS ONE* 7 (2012), e41806, <https://doi.org/10.1371/journal.pone.0041806>. Preprint version: arXiv:1112.2588 (2011), main text Sections 2–4 and supplementary Section S.1, <https://doi.org/10.48550/arXiv.1112.2588>.
