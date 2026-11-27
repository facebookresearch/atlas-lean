# Catoni's PAC-Bayes bound

Let $\Theta$ and $\mathcal Z$ be measurable spaces, let a jointly measurable loss
$\ell : \Theta \times \mathcal Z \to \mathbb{R}$ take values in $[0, C]$, let $n \ge 1$ and let
$S = (S_1, \dots, S_n)$ be an i.i.d. sample from a probability measure $D$ on $\mathcal Z$, and let
$\pi$ be a prior probability measure on the parameter space $\Theta$. Write
$R(\theta) = \int \ell(\theta, z) \, dD(z)$ for the risk and
$r_S(\theta) = \frac1n \sum_{i} \ell(\theta, S_i)$ for the empirical risk. For every $\lambda > 0$
and $\delta \in (0, 1)$, with probability at least $1 - \delta$ over $S$, every probability
measure $\rho$ on $\Theta$ with $\mathrm{KL}(\rho \,\|\, \pi) < \infty$ satisfies

$$\int R \, d\rho \le \int r_S \, d\rho + \frac{\lambda C^2}{8n} + \frac{\mathrm{KL}(\rho \,\|\, \pi) + \log(1/\delta)}{\lambda}.$$

Here "with probability at least $1 - \delta$" means that the outer measure of the bad event is at
most $\delta$; this holds for every $\delta > 0$ (the bound is trivial for $\delta \ge 1$), and
the restriction to $\mathrm{KL}(\rho \,\|\, \pi) < \infty$ loses nothing, since otherwise the right
side is infinite.

Proof: by Hoeffding's lemma, $E_S \, e^{\lambda (R(\theta) - r_S(\theta))} \le e^{\lambda^2 C^2 / (8n)}$ for
each $\theta$; integrating against $\pi$ and exchanging the integrals (Tonelli) bounds
$E_S \int e^{\lambda (R - r_S)} d\pi$; Markov's inequality makes $\int e^{\lambda(R - r_S)} d\pi$ at most
$e^{\lambda^2 C^2/(8n)} / \delta$ outside an event of probability $\delta$; and on the complement the
Donsker–Varadhan inequality $\lambda \int (R - r_S) \, d\rho \le \mathrm{KL}(\rho \,\|\, \pi) + \log \int e^{\lambda(R - r_S)} d\pi$
holds for all $\rho$ at once.

## Informally uses

- [Donsker–Varadhan inequality for bounded test functions](../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/integral-sub-log-integral-exp-le-to-real.md):
  Alquier's proof applies Donsker and Varadhan's variational formula (his Lemma 2.2) to
  $\lambda (R - r_S)$.

## Sources

- P. Alquier, User-friendly introduction to PAC-Bayes bounds, *Foundations and Trends in Machine Learning* 17 (2024), arXiv:2110.11216, Theorem 2.1 (Catoni's bound) and its proof.
