# Total-variation error bound for describing function approximations

**Describing function.** Drive a system with input $u(t)=u_0+b\sin\omega t$ and suppose its output $f(t)$ is (asymptotically) periodic with frequency $\omega_0=\omega$. Writing $f(t)=\sum_{n\in\mathbb Z}C_ne^{jn\omega_0t}$ with $C_n=\frac1T\int_{-T/2}^{T/2}f(t)e^{-jn\omega_0t}\,dt$, the describing function at $(u_0,b,\omega)$ is the complex gain of the first harmonic relative to the input, $N=2C_1/(-jb)$ (amplitude ratio and phase shift of the fundamental), and the first-harmonic approximation is $f_1(t)=\sum_{|n|\le1}C_ne^{jn\omega_0t}$. For a static nonlinearity $N$ depends only on the amplitude; for dynamic biomolecular nonlinearities it also depends on frequency and bias.

**Total variation.** For $f:[a,b]\to\mathbb R$, $V_a^b(f)=\sup_M\sum_k|f(x_{k+1})-f(x_k)|$ over partitions $M$ of $[a,b]$; it is additive over adjacent intervals and $V(cf)=|c|V(f)$.

**Theorem 1 (Fourier tail bound).** If $f$ is periodic with frequency $\omega_0$ and its total variation over one period is at most $V$, the mean-square error of the truncation to the first $m$ harmonics satisfies

$$\epsilon_m^2=\|f-f_m\|_2^2\le\frac{V^2}{\pi\,\omega_0\,m}.$$

In particular the describing-function (first-harmonic) error obeys $\epsilon_1^2\le V^2/(\pi\omega)$.

**Consequences.**

- A saturation of slope $k$ and level $ka$ driven with amplitude $A>a$ has $V=4ka$ per period, so $\epsilon_1^2\le(4ka)^2/(\pi\omega)$; a relay with hysteresis and output levels $\pm D$ has $\epsilon_1^2\le(4D)^2/(\pi\omega)$.
- A periodic output that is monotone between one minimum and one maximum per period has $V=2(\max f-\min f)$. The source prints this for every signal: "for any real periodic signal, the total variation over a period is bounded and is four times of the amplitude of the signal" (Section 3.1); the page restricts it to such unimodal signals, since a signal with several local maxima per period has total variation larger than $2(\max f-\min f)$ (e.g. $\sin t+\sin 3t$). For a biomolecular output bounded by a conserved total (e.g. an enzyme-modified fraction $0\le A_1\le A_T$), this yields a bound from the conservation law alone, without simulating the trajectory.
- In harmonic-balance limit-cycle analysis, replacing $N$ by the uncertainty set $N(1\pm e)$ in $1+N(A)G(j\omega)=0$ gives an interval of predicted amplitudes. For the Van der Pol oscillator the nominal prediction is $\omega=1$, $A=2$, and the error band gives amplitudes between about $1.53$ and $3.72$, which bracket the true oscillation for moderate damping.

## Expansion

Theorem 1 is the classical estimate that Fourier coefficients of a function of bounded variation decay like $|C_n|\le V/(2\pi|n|)$, so the tail $\sum_{|n|>m}|C_n|^2$ is $O(V^2/m)$; multiplying by the period converts it into the integrated square error. The describing function for biomolecular systems is computed by simulating to the periodic regime and projecting onto the fundamental. Compared with standard Jacobian linearisation it captures finite-amplitude effects: for an ultrasensitive covalent-modification cycle the describing-function gain at finite input amplitude is lower and the bandwidth higher than the linearisation predicts, and for a hysteretic positive-feedback switch (where no single operating point exists) the low-frequency response has constant magnitude and linearly decreasing phase, i.e. it behaves like a pure delay.

## Sources

- Dey A, Sen S, "Describing function-based approximations of biomolecular systems" (2018), Section 3 (Definition 1, Theorem 1 quoted from the Fourier-series literature, Examples 4-5 and Example 1 continued) and Section 4 (Van der Pol and repressilator limit-cycle analysis); the general total-variation statement for unimodal periodic signals is stated here in corrected form, <https://doi.org/10.1049/iet-syb.2017.0026>, PMCID PMC8687285.
