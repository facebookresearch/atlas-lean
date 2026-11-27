# Moment comparisons and tail bounds for low-degree functions

For $f : \{-1,1\}^n \to \mathbb{R}$ of degree at most $k$: (1) for $0 < p \le 2$, $\|f\|_2 \le e^{k(2/p - 1)}\|f\|_p$, in particular $\|f\|_2 \le e^k \|f\|_1$; (2) if $k \ge 1$ and $\|f\|_2 > 0$, then $\Pr[|f| \ge t\|f\|_2] \le \exp\big(-\frac{k}{2e} t^{2/k}\big)$ for every $t \ge (2e)^{k/2}$. (Both hypotheses of (2) are needed: for $f = 0$ the event has probability $1$, and for $k = 0$ the exponent $2/k$ is undefined; a nonzero constant has $\Pr[|f| \ge t\|f\|_2] = 0$ for $t > 1$.)

## Proof sketch

(1) For $q > 2$ write $\frac12 = \frac\theta p + \frac{1-\theta}{q}$; Hölder gives $\|f\|_2 \le \|f\|_p^{\theta}\|f\|_q^{1-\theta}$, and the hypercontractive bound $\|f\|_q \le \sqrt{q-1}^{\,k}\|f\|_2$ then gives $\|f\|_2 \le (q-1)^{k(1-\theta)/(2\theta)}\|f\|_p$. Take the limit $q \downarrow 2$, where the factor tends to $e^{k(2/p-1)}$ (O'Donnell, Thm. 9.22 and Ex. 9.15; the computation is the same for $0 < p < 1$). (2) Normalize $\|f\|_2 = 1$; Markov's inequality on $|f|^q$ with $q = t^{2/k}/e \ge 2$ and $\mathbb{E}|f|^q \le (q-1)^{kq/2} \le q^{kq/2}$ (O'Donnell, Thm. 9.23).

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)
- [Hypercontractivity Theorem (Bonami–Beckner)](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/hypercontractivity-theorem.md)
- [L^p seminorms under a probability measure increase with the exponent](../fourier-expansion-supplements/lp-norms-increase-with-p.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
