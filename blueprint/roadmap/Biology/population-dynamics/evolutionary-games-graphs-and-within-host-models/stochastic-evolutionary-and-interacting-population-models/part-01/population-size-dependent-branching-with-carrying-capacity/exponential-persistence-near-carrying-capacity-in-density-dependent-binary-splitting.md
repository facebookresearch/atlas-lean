# Exponential persistence near carrying capacity in density-dependent binary splitting

**Model.** Individuals live one generation. In a generation of size $z$, each individual independently has two children with probability $p(z) = K/(K+z)$ and none otherwise, so that

$$Z_{n+1} \mid Z_n = z \;\sim\; 2\,\mathrm{Bin}\!\left(z, \frac{K}{K+z}\right).$$

The mean offspring number $2K/(K+z)$ is above $1$ for $z < K$, equal to $1$ at the carrying capacity $z = K$, and below $1$ for $z > K$. The population dies out with probability one.

**Theorem.**

1. (Lower band.) Fix $0 < d < 1$ and let $\tau^K$ be the first generation in which $Z_n \le dK$. With

$$c = \frac{d(1-d)^2}{8(1+d)},$$

for every $K > 0$, every $n \in \mathbb N$ and every starting size $z \ge dK$,

$$\mathbb P_z(Z_1 > dK) \ge 1 - e^{-cK}, \qquad \mathbb P_z(\tau^K > n) \ge (1 - e^{-cK})^n, \qquad \mathbb E_z[\tau^K] \ge e^{cK}.$$

2. (Upper band.) For $d > 1$, with $c_1 = (d-1)^2/(8(d+1))$ and $\tau^K$ the first generation with $Z_n \ge dK$, for every $z \le dK$: $\mathbb P_z(Z_1 < dK) \ge 1 - e^{-c_1K}$, $\mathbb P_z(\tau^K > n) > (1 - e^{-c_1K})^n$ and $\mathbb E_z[\tau^K] > e^{c_1K}$.

For $d = 1/2$, $c = 1/96 \approx 0.01$. A population with carrying capacity $K = 1000$ that has reached half its capacity therefore persists on average for at least $e^{10.4}$, about $3\times 10^4$ generations. In this model, demographic stochasticity alone is not a short-term extinction risk once a population is established.

This is an explicit instance of the general picture for population-size-dependent branching processes that are supercritical below $K$, critical at $K$ and subcritical above it. Starting small, they reach size $dK$ with positive probability within $O(\log K)$ time. The density $Z_t/K$ then stays uniformly close to $1$ on compact time intervals and leaves a neighbourhood of $1$ only after a time exponentially large in $K$. Final extinction from $aK$, given that the maximum stays below $bK$, takes $O(\log K)$ time.

## Expansion

With $x = z/K$ and $f(x) = 2x/(1+x)$, the conditional mean of $Z_1$ is $Kf(x)$, and $f(x) > f(d) > d$ for $x > d$. A Chernoff/Janson lower-tail bound for the binomial, $\mathbb P(X \le kp - a) \le e^{-a^2/(2kp)}$, applied with $a = (2zp(z) - dK)/2$, gives $\mathbb P_z(Z_1 \le dK) \le \exp(-K(f(x)-d)^2/(4f(x)))$. The exponent is increasing in $f(x) > d$, so it is at least its value at $x = d$, which is $c$. The Markov property and induction give the geometric bound on $\tau^K$, and summing tail probabilities gives $\mathbb E[\tau^K] \ge e^{cK}$. The upper band uses $k - \mathrm{Bin}(k,p) \overset{d}{=} \mathrm{Bin}(k,1-p)$ and the same inequality.

## Sources

- Kais Hamza, Peter Jagers, Fima C. Klebaner, "On the Establishment, Persistence, and Inevitable Extinction of Populations", arXiv (2014). Sections "Extinction or growth" and "An era of stable size" (establishment in $O(\log K)$ time, law of large numbers, exponential exit time), Section "A simple example with far-reaching conclusions" (binary-splitting theorems with the constants $c$ and $c_1$), and Section "The time of decay". <https://doi.org/10.48550/arXiv.1410.2973>. Published version: Journal of Mathematical Biology 72(4) (2016), 797–820, <https://doi.org/10.1007/s00285-015-0903-2>; locators above refer to the arXiv version.
