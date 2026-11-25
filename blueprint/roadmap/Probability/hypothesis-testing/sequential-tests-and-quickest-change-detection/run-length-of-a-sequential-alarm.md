# Run length of a sequential alarm

In the sequential test of a defect rate, the alarm time $\tau$ takes values in $\mathbb{N} \cup \{\infty\}$. Under $P_\theta$,
$P(\tau < \infty) \le \alpha < 1$, so $P(\tau = \infty) \ge 1 - \alpha > 0$ and the expected run length, as an extended expectation,
is infinite, while the truncated run length satisfies $E[\min(\tau, H)] \le H$ for every horizon $H \in \mathbb{N}$. Run lengths
conditional on an alarm, or after a restart, have other laws and need their own assumptions. When the data violate the null
model the alarm can be certain: if $X_i = 1$ for all $i$, $\theta = 1/2$ and $q = 3/4$, then $E_n = (3/2)^{n+1}$, which eventually
exceeds $1/\alpha$.

## Depends on

- [Sequential test of a defect rate](sequential-test-of-a-defect-rate.md)

## Proof depends on

## Sources

- A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, Game-theoretic statistics and safe anytime-valid inference, *Statistical Science* 38 (2023), Section 2.5, Ville's inequality, Equation (8), <https://arxiv.org/abs/2210.01948>.
- NIST/SEMATECH *e-Handbook of Statistical Methods*, Section 6.3.2, Shewhart control limits $\mu_w \pm k\sigma_w$ and the average run length, <https://www.itl.nist.gov/div898/handbook/pmc/section3/pmc32.htm>.
