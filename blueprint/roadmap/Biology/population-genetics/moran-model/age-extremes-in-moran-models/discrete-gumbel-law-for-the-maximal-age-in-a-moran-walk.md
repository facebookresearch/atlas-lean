# Discrete Gumbel law for the maximal age in a Moran walk with resets

**Model.** A Moran walk of length $n$ starts at $0$ and at each step either moves up by $1$ with probability $p \in (0,1)$ or is reset to $0$ with probability $q = 1-p$. It records the age of one individual in a Moran-type population of constant size: each unit of time the individual survives (its age increases by one) or dies and is replaced by a newborn of age $0$. Let $Y_n$ be the final altitude (the current age) and $H_n = \max_{k \le n}$ (altitude at step $k$), the **height** (the oldest age reached up to time $n$).

**Final altitude.** $\mathbb{P}(Y_n = k) = q p^k$ for $0 \le k < n$ and $\mathbb{P}(Y_n = n) = p^n$: a truncated geometric law.

**Theorem (height distribution).** Uniformly in $h \in [0,n]$,

$$\mathbb{P}(H_n \le h) = \exp\big(-q\,n\,p^{h+1}\big)\,\big(1 + o(1)\big),$$

with an explicit error term of order $(\ln n)^3/n$. Consequently $H_n$ has no continuous limit law: writing $\alpha(n) = p^{-\{\ln n/\ln(1/p)\}} \in [1, 1/p)$, with $\{\cdot\}$ the fractional part,

$$\mathbb{P}\Big(H_n \le \Big\lfloor \frac{\ln n}{\ln(1/p)}\Big\rfloor + k\Big) = \exp\big(-q\,\alpha(n)\,p^{k+1}\big)(1+o(1))$$

uniformly in $k$, a discrete Gumbel law whose shape oscillates with $\ln n$. The distribution of $H_n$ is unimodal with mode $h^*(n)$, the integer closest to $c^*(n)\ln n/\ln(1/p)$ with $c^*(n) = 1 - \ln(\ln(1/p)/q^2)/\ln n$, and $\mathbb{P}(H_n = h^*(n)) \sim p^{p/q} - p^{1/q}$.

**Theorem (average height).**

$$\mathbb{E}[H_n] = \frac{\ln n}{\ln(1/p)} - \frac{\gamma}{\ln p} - \frac12 - \frac{\ln q}{\ln p} + \frac{Q(\ln(qn))}{\ln p} + o(1),$$

where $\gamma$ is Euler's constant and $Q(x) = \sum_{k \ne 0}\Gamma(s_k)e^{-s_k x}$, $s_k = 2ik\pi/\ln p$, is a real, infinitely differentiable Fourier series of period $\ln(1/p)$ and tiny amplitude.

## Expansion

The walk is a renewal process: excursions between resets have i.i.d. geometric lengths $G$ with $\mathbb{P}(G \ge h) = p^{h}$, and about $qn$ excursions occur by time $n$. The height is the maximum of these lengths, so $\mathbb{P}(H_n \le h) \approx (1 - p^{h+1})^{qn} \approx \exp(-qnp^{h+1})$. Maxima of geometric variables do not converge to a Gumbel law; they track it along subsequences, hence the sawtooth $\alpha(n)$ and the periodic correction $Q$. The paper derives the exact generating function of walks of bounded height (algebraic, by the kernel method, equivalently Lagrange interpolation) and extracts asymptotics with singularity analysis and Mellin transforms.

## Sources

- Rafik Aguech, Asma Althagafi and Cyril Banderier, "Height of walks with resets, the Moran model, and the discrete Gumbel distribution", Sém. Lothar. Combin. 87B (2023), Article 12 (the journal assigns no DOI), <https://www.mat.univie.ac.at/~slc/wpapers/lattpath/12.html>. Numbering follows the arXiv version, arXiv:2311.13124 (2023): Section 2 ("Final altitude: asymptotics"), Section 3 ("Distribution of the height of Moran walks"), Section 4 ("Average height"), Section 5 (Moran model), <https://doi.org/10.48550/arXiv.2311.13124>.
