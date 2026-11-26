# Spike-count condition for identifying a dendritic filter from integrate-and-fire spikes

Work in the setting of the [conditional duality](conditional-duality-between-channel-identification-and-time-decoding.md): inputs lie in the space $\mathcal H$ of trigonometric polynomials of bandwidth $\Omega$, order $L$ and period $T = 2\pi L/\Omega$ with orthonormal basis $e_l$, a filter $h \in L^1(\mathbb{R})$ supported in $[0, T]$ feeds an ideal IAF neuron with known bias $b$, capacitance $C$ and threshold $\delta$, and spike intervals give measurements $q_k = C\delta - b(t_{k+1} - t_k)$.

(Single stimulus.) If an input $u = \sum_l u_l e_l$ makes the neuron fire $n \ge 2L + 2$ spikes in $[0, T]$ and the matrix $\Phi$ below has full column rank $2L + 1$, then the filter projection is recovered exactly as $(\mathcal P h)(t) = \sum_{l=-L}^{L} h_l e_l(t)$ with $\mathbf h = \Phi^{+}\mathbf q$, where $\Phi^{+}$ is the Moore–Penrose pseudoinverse, $[\mathbf q]_k = q_k$, and $\Phi$ is $(n-1) \times (2L+1)$ with

$$[\Phi]_{kl} = \begin{cases} u_0\,(t_{k+1} - t_k), & l = 0,\\[4pt] u_l\, \dfrac{L\sqrt T}{j l \Omega}\,\big(e_l(t_{k+1}) - e_l(t_k)\big), & l \ne 0 . \end{cases}$$

(Several stimuli.) If $N$ linearly independent inputs $u^1, \dots, u^N \in \mathcal H$ produce $n_i$ spikes each with total $n = \sum_i n_i \ge 2L + N + 1$, stacking the per-stimulus blocks $\Phi^i$ and measurement vectors $\mathbf q^i$ gives $\mathbf q = \Phi\mathbf h$, and $\mathcal P h$ is recovered as $\mathbf h = \Phi^{+}\mathbf q$ when $\Phi$ has rank $2L + 1$. A neuron that fires too sparsely for any single stimulus can thus be compensated by more stimuli.

(Convergence to the filter.) If $\int_0^T |h|^2 < \infty$, then $\mathcal P h \to h$ in $L^2[0, T]$ and almost everywhere as $\Omega, L \to \infty$ with $T$ fixed.

## Depends on

- [Conditional duality between channel identification and time decoding](conditional-duality-between-channel-identification-and-time-decoding.md)

## Proof depends on

- [Parseval's identity on the circle](../../../../Analysis/harmonic-analysis/fourier-series/convergence-of-fourier-series/parseval-identity-on-the-circle.md)
- [Carleson's theorem](../../../../Analysis/harmonic-analysis/fourier-series/convergence-of-fourier-series/carleson-ae-tendsto.md)

## Expansion

Since $\mathcal P h \in \mathcal H$, each measurement $q_k = \langle \mathcal P h, \phi_k\rangle = \sum_l h_l \overline{\phi_{l,k}}$ is linear in the $2L + 1$ unknown coefficients, so recovery is solving a linear system; full rank needs at least $2L + 1$ measurements, i.e. $2L + 2$ spikes for one stimulus, or $2L + N + 1$ spikes over $N$ stimuli because each stimulus loses one interval. The entries of $\Phi$ are $\sqrt T\, u_l \int_{t_k}^{t_{k+1}} e_l$ evaluated in closed form. For convergence, $\mathcal P h$ is exactly the $L$-th partial Fourier sum of $h$ on $[0, T]$, so $L^2$ convergence is Parseval and almost-everywhere convergence is Carleson's theorem. Requiring inter-spike intervals at most $T/(2L+2)$ and letting $L \to \infty$ recovers a Nyquist-type condition $C\delta < \pi(b - c)/\Omega$ when $|v| \le c < b$. These are Lemma 9, Theorem 11 and Proposition 12 of the source, which also gives a multi-input version for filter banks driving an asynchronous sigma-delta modulator (its Theorem 14).

## Sources

- A. A. Lazar, Y. B. Slutskiy, Channel identification machines, Comput. Intell. Neurosci. 2012 (2012), 209590, Lemma 9, Remark 10, Theorem 11, Proposition 12, Eqs. (10)–(13), (18). <https://doi.org/10.1155/2012/209590> (PMCID: PMC3505648)
