# Impulsive coffee leaf rust model with harvest pulses and threshold biocontrol

**Base model.** Susceptible leaves $S$, infected leaves $I$, fungal spores $U$ and spore-eating predators $P$ (biocontrol agents) follow

$$\dot S=\Lambda-\omega\nu SU-\mu S,\qquad \dot I=\omega\nu SU-(\mu+d)I,\qquad \dot U=\gamma I-\nu SU-\mu_UU-\delta UP,\qquad \dot P=\eta\delta UP-\mu_PP,$$

where spores land on leaves at rate $\nu SU$ (consumed in the process), a fraction $\omega$ germinate, infected leaves shed spores at rate $\gamma$ and die faster ($d$), and predators convert eaten spores with efficiency $\eta$. With $S^0=\Lambda/\mu$,

$$\mathcal R_0=\frac{\gamma\nu\omega S^0}{(\mu+d)(\nu S^0+\mu_U)},$$

the disease-free equilibrium is globally asymptotically stable if $\mathcal R_0<1$ and unstable otherwise, and for $\mathcal R_0>1$ there is a predator-free endemic equilibrium with $U^\star=\frac{(\Lambda\nu+\mu\mu_U)(\mathcal R_0-1)}{\mu_U\omega\nu}$, plus a coexistence equilibrium with predators.

**Yearly harvest pulses.** A single harvest and pruning at times $nT$ multiplies each compartment by $\varphi_k\in(0,1)$. The periodic disease-free solution then has $S$ relaxing between pulses, and Floquet theory gives the threshold

$$\mathcal R=\frac{\varphi_I}{2\beta}\Big[(\beta+k_1-k_2)e^{\lambda_1T}+(\beta-k_1+k_2)e^{\lambda_2T}\Big],$$

with $k_1=\mu+d$, $k_2=\nu S^0+\mu_U$, $\beta=\sqrt{(k_1-k_2)^2+4\gamma\omega\nu S^0}$ and $\lambda_{1,2}=-\frac{k_1+k_2}2\mp\frac\beta2$. The periodic disease-free solution is locally asymptotically stable if $\mathcal R<1$ and unstable if $\mathcal R>1$, and globally asymptotically stable when $\mathcal R_0<1$.

**Threshold biocontrol.** Farmers release $\Lambda_P$ predators (at most once a year) when infected leaves reach a level $I_s$, giving a model with both fixed-time and state-dependent impulses. Simulations show low thresholds hold infection down for several years but, because spores are never eradicated, infection recurs, and high thresholds lose control.

**Theorem (extinction probability).** Near the disease-free state, infected leaves and spores form a two-type branching process with offspring generating functions

$$f_I(z)=\frac{\gamma z_Uz_I+\mu+d}{\gamma+\mu+d},\qquad f_U(z)=\frac{\omega\nu S^0z_I+\nu S^0+\mu_U}{\omega\nu S^0+\nu S^0+\mu_U}.$$

Starting from $i_0$ infected leaves and $u_0$ spores, $\mathbb P_{\mathrm{ext}}=q_I^{\,i_0}q_U^{\,u_0}$, where $q=(q_I,q_U)$ is the minimal fixed point of $f$ in $[0,1]^2$: $q=\mathbf 1$ if $\mathcal R_0\le1$, and if $\mathcal R_0>1$ there is a unique fixed point $\mathbf 0<q<\mathbf 1$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)
- [Branching process approximation of early epidemics](../branching-process-approximation-of-early-epidemi/README.md)

## Expansion

The next-generation matrix has the single transmission entry $\omega\nu S^0$ (spore to infected leaf) and transfer matrix with leaf removal $\mu+d$, spore production $\gamma$ and spore removal $\nu S^0+\mu_U$, so $\mathcal R_0$ is the expected number of spores shed by one infected leaf times the probability that a spore germinates before being lost. Between harvests the linearized $(I,U)$ system has eigenvalues $\lambda_{1,2}$, and the harvest pulses act multiplicatively on the infected compartments, so the spectral radius of the monodromy matrix gives $\mathcal R$. The extinction result is the classical multitype Galton-Watson theorem: the mean matrix is primitive and the process non-singular, so the extinction vector is $\mathbf 1$ iff the Perron root of the mean matrix, equivalent to $\mathcal R_0\le1$, is at most one.

## Sources

- C. Djuikem, J. Arino, "Threshold-based impulsive biocontrol for coffee leaf rust", arXiv:2504.01055 (2025), Section 2.1 (base model, $\mathcal R_0$, Lemmas 1-2), Section 2.2 (impulsive model, threshold $\mathcal R$, Lemma 3, Theorem 4), Section 2.3 (threshold control) and Section 3.2 (Theorem 5), <https://doi.org/10.48550/arXiv.2504.01055>.
