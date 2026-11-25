# Tail bound for the χ²ₙ distribution

Let $Z_1, \dots, Z_n$ be independent standard normal variables. For every $t \in (0, 1)$,

$$\mathbb{P}\Big(\Big|\frac1n \sum_{k=1}^n Z_k^2 - 1\Big| \ge t\Big) \le 2 e^{-n t^2 / 8}.$$

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3, the χ² tail example.
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Example 3.8.

## Background

- [A centred χ²₁ variable is sub-exponential with parameters (2, 4)](has-subexponential-mgf-sq-sub-one-gaussi.md), [sums of independent sub-exponential variables](sum-of-i-indep-fun.md) and the [Gaussian regime of the sub-exponential tail bound](measure-real-ge-le-of-le.md): the source's proof combines them.
