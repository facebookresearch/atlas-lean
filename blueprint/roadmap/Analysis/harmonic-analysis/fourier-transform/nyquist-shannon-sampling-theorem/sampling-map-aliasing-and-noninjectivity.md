# The sampling map: aliasing and noninjectivity

For $T > 0$ and a function $x : \mathbb{R} \to \mathbb{C}$, the sampling map gives the sequence $(S_T x)_n = x(nT)$, $n \in \mathbb{Z}$.

1. **Aliasing.** For every real frequency $f$ and every integer $k$, the complex exponentials $t \mapsto e^{2\pi i f t}$ and $t \mapsto e^{2\pi i (f + k/T) t}$ have the same samples: $e^{2\pi i (f + k/T) nT} = e^{2\pi i f nT}$ for all $n$.
2. **Noninjectivity.** The function $x(t) = \sin(\pi t / T)$ is smooth and bounded, and $S_T x = 0$, but $x(T/2) = 1$. So $S_T$ is not injective on continuous (or smooth, bounded) functions. More generally, $S_T$ identifies any two functions whose difference vanishes on $T\mathbb{Z}$.
3. **Periodic signals.** If $x$ is $NT$-periodic for an integer $N \ge 1$, then $S_T x$ is $N$-periodic: $(S_T x)_{n+N} = (S_T x)_n$. Its restriction to $\{0, \dots, N-1\}$ is therefore a vector on $\mathbb{Z}/N\mathbb{Z}$, to which the discrete Fourier transform applies.

Part 1 holds because $e^{2\pi i k n} = 1$. Part 2 holds because $\sin(\pi n) = 0$ and $\sin(\pi/2) = 1$. For part 3, $x((n + N)T) = x(nT + NT) = x(nT)$. Recovery from samples needs an extra hypothesis such as a band limit.

## Background

- [Sampling theorem for square-integrable band-limited functions](sampling-theorem-for-square-integrable-band-limited-functions.md): functions band-limited to $[-B, B]$ with $2BT \le 1$ are determined by their samples

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 5.4.2: sampling a function at $t = nT$, the spectral replicas at multiples of $2\pi/T$ and aliasing (Figure 5.24, p. 457, and the paragraph "Aliasing", p. 460), and Section 5.3, aliasing of the frequency $\omega$ to $\omega - 2\pi k/N$ (Figure 5.17, pp. 440–441).
