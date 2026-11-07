# Majority Is Least Stable fails in every odd dimension at least five

For every odd natural
number $n \ge 5$, the Majority Is Least Stable conjecture in $n$ variables fails: there are a
linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ and a real number $\rho$ with
$0 \le \rho \le 1$ such that $\mathrm{Stab}_\rho[f] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$, where
$\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the majority function.

Biswas and Sarkar exhibit, for every odd $n \ge 5$, a linear threshold function $g_n$ with
$\mathrm{Stab}_\rho[g_n] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for all small $\rho > 0$. The
conjecture holds for $n = 1$ and $n = 3$; those cases are not formalized here.

## Sources

- R. O'Donnell, Open problems in analysis of Boolean functions, arXiv:1204.6447 (2012), 'Majority Is Least Stable Conjecture' (Benjamini, Kalai, Schramm); resolution: A. Biswas, P. Sarkar, On the "majority is least stable" conjecture, Inform. Process. Lett. 179 (2023), 106295, arXiv:2202.09024, Theorem 2 of arXiv:2202.09024v2: the conjecture is true for n = 1 and n = 3 and false for every odd n ≥ 5; for odd n ≥ 5 the linear threshold function g_n(x) = sgn(2(x₁ + ⋯ + x_{n-3}) + x_{n-2} + x_{n-1} + x_n) has W⁰[g_n] = 0 and W¹[g_n] < W¹[Maj_n] (Lemmas 3 and 4), hence Stab_ρ[g_n] < Stab_ρ[Maj_n] for all small ρ > 0 (Lemma 1); the case n = 5 is V. Jain, arXiv:1703.07657, https://doi.org/10.1016/j.ipl.2022.106295.
