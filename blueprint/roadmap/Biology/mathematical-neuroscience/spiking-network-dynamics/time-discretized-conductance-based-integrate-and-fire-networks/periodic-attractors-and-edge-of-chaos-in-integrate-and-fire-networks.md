# Periodic attractors and the edge of chaos in integrate-and-fire networks with conductance synapses

**Setting.** A network of $N$ integrate-and-fire neurons with conductance-based synapses has membrane potentials $\mathbf V=(V_1,\dots,V_N)$ in a compact phase space $\mathcal M$, firing threshold $\theta$, reset after a spike, and constant external input. Spike times are known only to a finite precision $\delta>0$, which can be arbitrarily small. So spikes take effect at multiples of $\delta$, and the dynamics becomes a piecewise-smooth map $\mathbf V(t+1)=F(\mathbf V(t))$. Between spikes, the map is affine in $\mathbf V$ and contracting, with conductances depending on the past raster plot $\tilde\omega$. Its singularity set is $\{V_i=\theta\}$. Let $\Omega$ be the $\omega$-limit set of $\mathcal M$, and define the distance from the attractor to the singularity set

$$d(\Omega,\mathcal S)=\inf_{\mathbf V\in\Omega}\ \inf_{t\ge0}\ \min_{i}\ |V_i(t)-\theta| .$$

**Theorem.**

1. The domains of $\mathcal M$ on which the raster plot up to time $t$ is fixed are convex and connected. On each of them, $F^{t+1}$ is a non-uniform contraction with rate $\frac1{t+1}\sum_{s\le t}\log\sigma_k(s,\tilde\omega)<0$ in direction $k$.
2. Suppose there are $\epsilon>0$ and $T<\infty$ such that, for every initial condition, each neuron either fires within time $T$ or eventually stays below $\theta-\epsilon$ forever. Then $\Omega$ consists of finitely many periodic orbits, each of period at most $T$.
3. If $d(\Omega,\mathcal S)>0$, then $\Omega$ consists of finitely many stable periodic orbits of finite period. Trajectories on $\Omega$ are in one-to-one correspondence with their raster plots.

The number and periods of these orbits can be arbitrarily large, and they diverge as $d(\Omega,\mathcal S)\to0$. This defines the *edge of chaos* as the region of synaptic-weight space where $d(\Omega,\mathcal S)=0$.

## Proof sketch

Between threshold crossings the dynamics contracts phase space. Distinct behaviour can only arise from the partition of $\mathcal M$ into domains with different spike patterns, whose boundaries are the singularity set. If the attractor stays a positive distance from the threshold, then after a finite time $T$, which diverges as the distance shrinks, $F^T$ has a finite Markov partition. Each element is contracted into a single element, which forces eventually periodic dynamics with finitely many periodic orbits. Away from the edge of chaos, the raster plot determines the membrane-potential trajectory, so the neural code is entirely "in the spikes". Near the edge, transients and periods become longer than any observation time, and the dynamics is effectively chaotic. The quantity $d(\Omega,\mathcal S)$, estimated numerically, serves as an order parameter related to the entropy of the spike-train code. It allows the computational capacity of leaky integrate-and-fire and conductance-based models to be compared.

## Sources

- B. Cessac, T. Viéville, "On Dynamics of Integrate-and-Fire Neural Networks with Conductance Based Synapses", *Frontiers in Computational Neuroscience* 2 (2008), 1–20, <https://doi.org/10.3389/neuro.10.002.2008>. Preprint version: arXiv:0709.4370 (2007), Corollaries on convexity of the domains and non-uniform contraction, the lemma and theorem on $\omega$-limit sets consisting of finitely many periodic orbits, and the theorem on $d(\Omega,\mathcal S)>0$ (periodic attractors and raster-plot coding) together with the definition of the edge of chaos, <https://doi.org/10.48550/arXiv.0709.4370>.
