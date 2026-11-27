# Generic periodicity of the Beslon–Mazet–Soula spiking network

**Model (BMS).** Fix $N$ neurons, a synaptic weight matrix $W=(W_{ij})$, a threshold $\theta>0$, a leak $\gamma\in[0,1)$ and constant external currents $I^{\mathrm{ext}}_i$. With $Z(x)=\mathbf 1_{\{x\ge\theta\}}$ the firing indicator, membrane potentials evolve synchronously in discrete time by

$$
V_i(t+1)=\gamma V_i(t)\big(1-Z[V_i(t)]\big)+\sum_{j=1}^N W_{ij}Z[V_j(t)]+I^{\mathrm{ext}}_i,\qquad i=1,\dots,N .
$$

A neuron that fires is reset (its leaky memory is erased) and every neuron receives the synaptic input of the neurons that fired. On each cell of the partition by firing pattern $\eta\in\{0,1\}^N$ the map is affine with diagonal linear part $\gamma(1-\eta_i)$, hence a contraction; the only source of complexity is the singularity set $\mathcal S=\{V:\ V_i=\theta\ \text{for some } i\}$.

Let $\Omega$ be the $\omega$-limit set of the absorbing phase space, $d(\Omega,\mathcal S)=\inf_{V\in\Omega}\inf_{t\ge0}\min_i|V_i(t)-\theta|$ its distance to the threshold, and $V^{\sup}=\max_i\sup_{V}\limsup_{t\to\infty}V_i(t)$ the largest asymptotic potential. An orbit is a **ghost orbit** if some neuron never fires along it but $\limsup_t V_i(t)=\theta$.

**Theorem (asymptotic trichotomy; Cessac 2007, section on the general structure of the asymptotic dynamics).** Exactly one of the following holds.

1. **Neural death:** $V^{\sup}<\theta$. Then $V^{\sup}=\max_i I^{\mathrm{ext}}_i/(1-\gamma)$, $d(\Omega,\mathcal S)=\theta-V^{\sup}$, and $\Omega$ is a single fixed point with all neurons quiescent.
2. **Stable periodic regime:** $d(\Omega,\mathcal S)>0$ and $V^{\sup}>\theta$. Then $\Omega$ is a finite union of stable periodic orbits of finite period, and each orbit is coded one-to-one by its raster plot.
3. **Unstable periodic regime ("edge of chaos"):** $d(\Omega,\mathcal S)=0$, which forces $V^{\sup}\ge\theta$. The system shows a weak form of sensitivity to initial conditions and $\Omega$ may contain ghost orbits.

**Theorem (genericity; Cessac 2007, section on two theorems about the structure of the ω-limit set).** The set of parameters $(W,I^{\mathrm{ext}})$ for which $d(\Omega,\mathcal S)=0$ is non-generic, both topologically (contained in the complement of a countable intersection of open dense sets) and in Lebesgue measure. Hence for generic parameters the BMS network is eventually periodic: a finite automaton whose spike train is a deterministic function of finitely many past firing patterns, although periods and transients can be astronomically long near the edge of chaos.

**Random synapses.** For i.i.d. Gaussian weights with mean $0$ and variance $C^2/N$ and no external current, numerics show $d(\Omega,\mathcal S)$ collapsing toward $0$ across a critical line in the $(C,\gamma)$ plane, sharpening as $N$ grows: the "chaotic" regime reported for this model is a regime of exponentially long periodic orbits, numerically indistinguishable from chaos at finite observation times.

## Proof sketch

If $V^{\sup}<\theta$ nobody fires asymptotically and the affine contraction $V_i\mapsto\gamma V_i+I^{\mathrm{ext}}_i$ converges to $I^{\mathrm{ext}}_i/(1-\gamma)$. When the asymptotic dynamics stays a positive distance from the threshold, small perturbations never change the firing pattern, so nearby orbits share raster plots and the contraction collapses each admissible pattern sequence onto a periodic orbit; finitely many patterns are admissible because a neuron that fires has its past erased. A configuration with $d(\Omega,\mathcal S)=0$ requires some orbit to land exactly on, or accumulate on, the hyperplanes $V_i=\theta$; since $V_i(t)$ is an explicit affine function of $(W,I^{\mathrm{ext}})$ along a fixed pattern sequence, this imposes countably many codimension-one conditions on the parameters, which is a meagre, null set.

## Sources

- B. Cessac, "A discrete time neural network model with spiking neurons", *Journal of Mathematical Biology* 56 (2007), 311–345, <https://doi.org/10.1007/s00285-007-0117-3>. Preprint version: arXiv:0706.0077 (2007), sections "Asymptotic dynamics" (general structure of the asymptotic dynamics; two theorems about the structure of the ω-limit set; ghost orbits) and "Discussion" (random synapses), <https://doi.org/10.48550/arXiv.0706.0077>.
