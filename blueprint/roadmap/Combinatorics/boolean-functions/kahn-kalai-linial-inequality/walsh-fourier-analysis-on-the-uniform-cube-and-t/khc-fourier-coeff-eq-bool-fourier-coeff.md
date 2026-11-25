# Fourier coefficients for the two sign conventions agree up to sign

Let $n$ be a natural number, $f : \{0, 1\}^n \to \mathbb{R}$ and $S \subseteq \{1, \dots, n\}$. With $\chi_S(x) = \prod_{i \in S} (-1)^{x_i}$ and $\chi'_S(x) = \prod_{i \in S} (2x_i - 1)$,

$$2^{-n} \sum_{x} f(x)\, \chi_S(x) = (-1)^{\lvert S\rvert}\, 2^{-n} \sum_{x} f(x)\, \chi'_S(x).$$
