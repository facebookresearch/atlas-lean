# Asymptotic normality of short chords in non-crossing chord diagrams

Let $k \ge 2$. A linear $k$-chord diagram of length $kn$ is a partition of
$\{0, 1, \dots, kn - 1\}$ into $n$ blocks of size $k$, its chords; a chord is short when it
consists of $k$ consecutive integers. For natural numbers $n$ and $\ell$ let $T_{n,\ell}$ be the
number of non-crossing linear $k$-chord diagrams of length $kn$ with exactly $\ell$ short chords.
These numbers are determined by $T_{0,0} = 1$, $T_{0,\ell} = 0$ for $\ell \ge 1$, and the
recurrence

$$T_{n+1,\ell} = \sum_{\substack{m_1 + \dots + m_k = n \\ \ell_1 + \dots + \ell_k = \ell}}
\prod_{i=1}^{k} T_{m_i,\ell_i} - T_{n,\ell} + T_{n,\ell-1},$$

where the $m_i$ and $\ell_i$ are natural numbers and $T_{n,-1} = 0$. Put

$$\mu_n = \left(\frac{k-1}{k}\right)^{k-1} n, \qquad
\sigma_n^2 = \left(\frac{k-1}{k}\right)^{2k} \frac{k}{(k-1)^2}
\left(1 - 2k + (k-1)\left(\frac{k}{k-1}\right)^{k}\right) n,$$

and let $\sigma_n \ge 0$ be the square root of $\sigma_n^2$. Then for every real number $t$,

$$\frac{\sum_{\ell=0}^{n} T_{n,\ell}\, e^{t(\ell - \mu_n)/\sigma_n}}{\sum_{\ell=0}^{n} T_{n,\ell}}
\longrightarrow e^{t^2/2} \qquad (n \to \infty).$$

The left side is the moment generating function of $(\ell - \mu_n)/\sigma_n$, where $\ell$ is
the number of short chords of a uniformly random non-crossing linear $k$-chord diagram of length
$kn$. Its convergence to $e^{t^2/2}$, the moment generating function of the standard normal
distribution, implies that the number of short chords is asymptotically normal with mean $\mu_n$
and variance $\sigma_n^2$.

## Sources

- Donovan Young, "Linear k-Chord Diagrams", Journal of Integer Sequences 23 (2020), Article 20.9.1, Section 4.1, Theorem 28 (the recurrence for $T_{n,\ell}$ is Theorem 24), <https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.pdf>.
