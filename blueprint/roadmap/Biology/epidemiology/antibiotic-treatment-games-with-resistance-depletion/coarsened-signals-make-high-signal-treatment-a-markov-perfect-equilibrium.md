# Coarsened signals make high-signal treatment a Markov perfect equilibrium

**Model.** Two physicians each see one patient per period. A patient has a bacterial infection ($B$) with prior probability $P(B)$, independently across patients and periods. Each physician observes a private signal inducing a posterior $p \in [0,1]$ with continuous density $f > 0$ and distribution function $F$, so $P(B) = \int_0^1 p f(p)\,dp = \mathbb E[p]$. The antibiotic's effectiveness is $e = k\alpha$, where the E-state $k \in \{0,1,\dots,M\}$ counts remaining doses; each treatment lowers $k$ by one in the next period (both treat: $k \to k-2$; one treats: $k \to k-1$; none: $k$ stays), and the game ends at $k = 0$. With no harm from treating uninfected patients, treating a patient with posterior $p$ in E-state $k$ yields immediate expected payoff

$$u(p,k) = p\,k\alpha\,(r_2 - r_1),\qquad r_2 > r_1,$$

where $r_2$ and $r_1$ are the utilities of a bacterial infection with and without effective treatment; withholding yields $0$. Each physician maximizes the total payoff of his own patients; strategies are stationary Markov decision rules (treatment thresholds depending on $k$).

**Coarsening.** Replace the continuous signal by a dichotomous one with threshold $T$: signal $H$ if $p \ge T$ and $L$ if $p < T$, so $P(L) = F(T)$ and the induced posteriors are

$$p_H = \mathbb E[p \mid p \ge T],\qquad p_L = \mathbb E[p \mid p < T],\qquad (1 - F(T))\,p_H + F(T)\,p_L = P(B).$$

Each physician can then only treat everyone or treat only high-signal patients.

**Theorem.** Under the dichotomous signal, the symmetric profile in which both physicians treat only high-signal patients in every E-state is a Markov perfect equilibrium if and only if

$$p_H - p_L \ \ge\ (1 - F(T))\,p_H + F(T)\,p_L = P(B).$$

That is, the gap between the two posteriors must be at least the prior probability of infection; the condition involves only the information structure, not the utilities, the effectiveness levels or the depletion rate.

**Related results.** In the original continuous-signal game a symmetric pure-strategy Markov perfect equilibrium always exists, but the socially optimal symmetric policy (which, while effectiveness remains large, treats only patients with posterior close to $1$) is never an equilibrium.

## Expansion

By the one-stage-deviation principle it suffices to rule out a single-period deviation to treating everyone. Writing the continuation values recursively, that deviation is unprofitable in E-state $k$ iff a quantity proportional to $(1 + F(T))\,p_L - F(T)\,p_H$ is at most $v_{k-1} - v_{k-2}$, the value of one extra dose under the profile. The value is strictly increasing in $k$, so the right side is positive for $k \ge 2$ and zero at $k = 1$, where no future remains; the binding case $k = 1$ gives $F(T)p_H \ge (1+F(T))p_L$, which rearranges to the stated condition. Coarsening works by removing small deviations: with a continuous signal a physician can profitably treat a patient just below the threshold, whereas the coarse signal only allows the large deviation of treating everyone, which may not pay.

## Sources

- M. Diamant, S. Baruch, E. Kassem, K. Muhsen, D. Samet, M. Leshno, U. Obolski, "A game theoretic approach reveals that discretizing clinical information can reduce antibiotic misuse", Nature Communications 12:1148 (2021), Methods (model, Eqs (4)–(5), (11)–(17)), Theorems 2, 4, 6 and 9, Claim 8 and Eq (1), <https://doi.org/10.1038/s41467-021-21088-5>, PMCID PMC7895914.
