# Exposure statistics of single- and double-dose protocols under random missed doses

**Model.** Drug concentration follows one-compartment first-order elimination, $\frac{dc}{ds} = \frac{I(s)}{V} - k_e c$, with doses scheduled every $\tau$; let $\alpha = e^{-k_e\tau} \in (0,1)$ be the fraction remaining after one interval. At each scheduled time the patient remembers with probability $p \in (0,1)$, independently: $\xi_n \sim \mathrm{Bernoulli}(p)$ i.i.d. The amount taken is $D f_n$, where a *dosing protocol* $f_n = f(\xi_n, \xi_{n-1}, \dots, \xi_{n-m})$ depends on recent history:
- single dose: $f_n = \xi_n$;
- double dose: $f_n = 0$ if $\xi_n = 0$, $1$ if $\xi_n = \xi_{n-1} = 1$, and $2$ if $\xi_n = 1, \xi_{n-1} = 0$;
- boost: as double dose but taking $1 + b$ after a missed dose, $b \ge 0$;
- triple dose: $2$ after one missed dose, $3$ after two or more;
- all dose: take every missed dose.

At large times, the ratio $Z = \mathrm{AUC}/\mathrm{AUC}^{\mathrm{perf}} = C(t)/C^{\mathrm{perf}}(t)$ over a dosing interval (the same for every $t \in [0,\tau)$) compares the patient to perfect adherence. Its statistics are the mean $\mu = \mathbb{E}Z$, the relative root-mean-square deviation $\mathrm{dev} = \sqrt{\mathbb{E}(Z-1)^2}$ and the worst case $\lambda = \sup_\xi Z$.

**Theorem.**

$$\mu^{\mathrm{single}} = p, \qquad \mu^{\mathrm{double}} = p + p(1-p), \qquad \mu^{\mathrm{boost}} = p + b\,p(1-p), \qquad \mu^{\mathrm{triple}} = 3p - 3p^2 + p^3, \qquad \mu^{\mathrm{all}} = 1;$$

$$\mathrm{dev}^{\mathrm{single}} = \sqrt{\frac{1-p}{1+\alpha}}\sqrt{1 - \alpha(2p - 1)},$$

$$\mathrm{dev}^{\mathrm{double}} = \sqrt{\frac{1-p}{1+\alpha}}\sqrt{1 + p + (1 - 7p + 2p^2)\alpha + 2p^2(2-p)\alpha^2};$$

$$\lambda^{\mathrm{single}} = 1, \quad \lambda^{\mathrm{double}} = \frac{2}{1+\alpha}, \quad \lambda^{\mathrm{boost}} = \max\Big\{1, \frac{1+b}{1+\alpha}\Big\}, \quad \lambda^{\mathrm{triple}} = \frac{3}{1+\alpha+\alpha^2}, \quad \lambda^{\mathrm{all}} = \infty.$$

The coefficient of variation of the single-dose protocol is $\sqrt{\frac{1-\alpha}{1+\alpha}}\sqrt{p(1-p)}$.

## Proof sketch

The stationary concentration just after a dose is $\sum_{k\ge0}\alpha^k f_{n-k}$ (times $D/V$), a linear functional of the stationary Markov chain $X_n = (\xi_n, \dots, \xi_{n-m})$, so its first two moments follow from the stationary law $\pi(x) = p^{s(x)}(1-p)^{m+1-s(x)}$ and a geometric sum of autocovariances weighted by $\alpha^{|k|}$; dividing by the perfect-adherence value $1/(1-\alpha)$ gives $\mu$ and $\mathrm{dev}$. The worst case for the double-dose protocol is the pattern miss–take repeated, where each double dose arrives on top of a decayed level, giving $2/(1+\alpha)$. The formulas show a trade-off: making up missed doses raises mean exposure toward $1$ and can lower the deviation for long half-lives ($\alpha$ near $1$), but raises the peak exposure, which matters for drugs with narrow therapeutic windows.

## Sources

- Elijah D. Counterman and Sean D. Lawley, "What should patients do if they miss a dose of medication? A theoretical approach", *Journal of Pharmacokinetics and Pharmacodynamics* 48 (2021), 873–892, <https://doi.org/10.1007/s10928-021-09777-6>. Preprint version: arXiv:2102.05442 (2021), model and statistics (Section 2.1), Theorem 1 (Section 2.1.5), and in the Appendix Theorem 2, Corollaries 4–6 and Theorem 7, <https://doi.org/10.48550/arXiv.2102.05442>.
