# Discrete Gumbel law for the maximal age in a Moran walk with resets

**Model.** A Moran walk of length $n$ starts at $0$ and at each step either moves up by $1$ with probability $p \in (0,1)$ or is reset to $0$ with probability $q = 1-p$. It records the age of one individual in a Moran-type population of constant size: each unit of time the individual survives (its age increases by one) or dies and is replaced by a newborn of age $0$. Let $Y_n$ be the final altitude (the current age) and $H_n = \max_{k \le n}$ (altitude at step $k$), the **height** (the oldest age reached up to time $n$).

**Final altitude.** $\mathbb{P}(Y_n = k) = q p^k$ for $0 \le k < n$ and $\mathbb{P}(Y_n = n) = p^n$: a truncated geometric law.

**Theorem (height distribution).** Fix an integer $k$ and set $h_n = \lfloor \ln n/\ln(1/p)\rfloor + k$. Then

$$\mathbb{P}(H_n \le h_n) = \exp\big(-q\,n\,p^{h_n+1}\big)\,\big(1 + o(1)\big) = \exp\big(-q\,\alpha(n)\,p^{k+1}\big)(1+o(1)),$$

where $\alpha(n) = p^{-\{\ln n/\ln(1/p)\}} \in [1, 1/p)$, with $\{\cdot\}$ the fractional part; the same holds uniformly over any fixed bounded set of offsets $k$. Consequently $H_n$ has no continuous limit law: centered at $\lfloor \ln n/\ln(1/p)\rfloor$ it follows asymptotically a discrete Gumbel law whose shape oscillates with $\ln n$, and for each fixed $k$

$$\mathbb{P}\Big(H_n = \Big\lfloor \frac{\ln n}{\ln(1/p)}\Big\rfloor + k\Big) = \exp\big(-q\,\alpha(n)\,p^{k+1}\big) - \exp\big(-q\,\alpha(n)\,p^{k}\big) + o(1),$$

so the point masses near the center depend on the lattice phase $\alpha(n)$.

The source's Theorem 3.3 prints the first estimate with a relative error uniform in $h \in [0,n]$ (and the second uniformly in $k$), but its dominant-pole derivation, (3.2)–(3.6), gives the relative estimate only in the central window. The uniform relative form fails in the tail: for $p = q = 1/2$, $\mathbb{P}(H_n = 0) = 2^{-n}$ while the approximation gives $e^{-n/4}$. The source's further claim that the mode $h^*(n)$ carries mass $\sim p^{p/q} - p^{1/q}$ is not stated here: for $p = q = 1/2$ and $n = 2^m$ it selects $h^* = m-1$, whose mass by the display above tends to $e^{-1/2} - e^{-1} \approx 0.2387$, not $1/4$.

**Theorem (average height).**

$$\mathbb{E}[H_n] = \frac{\ln n}{\ln(1/p)} - \frac{\gamma}{\ln p} - \frac12 - \frac{\ln q}{\ln p} + \frac{Q(\ln(qn))}{\ln p} + o(1),$$

where $\gamma$ is Euler's constant and $Q(x) = \sum_{k \ne 0}\Gamma(s_k)e^{-s_k x}$, $s_k = 2ik\pi/\ln p$, is a real, infinitely differentiable Fourier series of period $\ln(1/p)$ and tiny amplitude.

## Expansion

The walk is a renewal process: excursions between resets have i.i.d. geometric lengths $G$ with $\mathbb{P}(G \ge h) = p^{h}$, and about $qn$ excursions occur by time $n$. The height is the maximum of these lengths, so $\mathbb{P}(H_n \le h) \approx (1 - p^{h+1})^{qn} \approx \exp(-qnp^{h+1})$. Maxima of geometric variables do not converge to a Gumbel law; they track it along subsequences, hence the sawtooth $\alpha(n)$ and the periodic correction $Q$. The paper derives the exact generating function of walks of bounded height (algebraic, by the kernel method, equivalently Lagrange interpolation) and extracts asymptotics with singularity analysis and Mellin transforms.

## Sources

- Rafik Aguech, Asma Althagafi and Cyril Banderier, "Height of walks with resets, the Moran model, and the discrete Gumbel distribution", Sém. Lothar. Combin. 87B (2023), Article 12 (the journal assigns no DOI), <https://www.mat.univie.ac.at/~slc/wpapers/lattpath/12.html>. Numbering follows the arXiv version, arXiv:2311.13124 (2023): Section 2 ("Final altitude: asymptotics"), Section 3 ("Distribution of the height of Moran walks"), Section 4 ("Average height"), Section 5 (Moran model), <https://doi.org/10.48550/arXiv.2311.13124>.
