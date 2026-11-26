# Bayesian sequential statistical model checking

**Specifications.** Let $SV$ be a finite set of real-valued model variables (species counts). Atomic propositions are predicates $e_1 \sim e_2$ with arithmetic expressions $e_1, e_2$ over $SV$ and $\sim \in \{\ge, \le, <, >, =\}$. *Bounded linear temporal logic* (BLTL) formulas are

$$\phi ::= AP \mid \phi_1 \vee \phi_2 \mid \phi_1 \wedge \phi_2 \mid \neg \phi_1 \mid \phi_1\, \mathbf U^{t}\, \phi_2,$$

interpreted on a trace $\sigma = (s_0, t_0), (s_1, t_1), \dots$ (state $s_k$ held for duration $t_k$, as produced by a stochastic simulation algorithm). With $\sigma^k$ the suffix from step $k$: $\sigma^k \models \phi_1 \mathbf U^t \phi_2$ iff there is $i \ge 0$ with $\sum_{0 \le l < i} t_{k+l} \le t$, $\sigma^{k+i} \models \phi_2$, and $\sigma^{k+j} \models \phi_1$ for all $0 \le j < i$. Derived operators: $\mathbf F^t \phi = \mathrm{true}\,\mathbf U^t \phi$ and $\mathbf G^t \phi = \neg \mathbf F^t \neg \phi$. Finite traces suffice to decide a BLTL formula.

**Test.** For a stochastic model $\mathcal M$ and formula $\phi$, the indicator $X = \mathbf 1\{\sigma \models \phi\}$ of a random trace is Bernoulli with unknown $p$. To decide

$$H_0: p \ge \theta \quad \text{vs} \quad H_1: p < \theta,$$

put a $\mathrm{Beta}(\alpha, \beta)$ prior on $p$ (with $P(H_0), P(H_1) > 0$), draw i.i.d. traces, and after $n$ traces with $x = \sum_{i=1}^n x_i$ successes compute the Bayes factor $\mathcal B_n = P(d \mid H_0)/P(d \mid H_1)$. Fix $T > 1$: accept $H_0$ if $\mathcal B_n > T$, accept $H_1$ if $\mathcal B_n < 1/T$, otherwise draw another trace.

**Proposition (closed-form Bayes factor).**

$$\mathcal B_n = \frac{P(H_1)}{P(H_0)} \left( \frac{1}{F_{(x+\alpha,\; n-x+\beta)}(\theta)} - 1 \right),$$

where $F_{(s,t)}$ is the $\mathrm{Beta}(s, t)$ distribution function.

**Theorem (error bound).** The probability that the sequential Bayesian test returns the wrong hypothesis is at most $1/T$.

## Expansion

By conjugacy the posterior of $p$ after $x$ successes in $n$ Bernoulli trials is $\mathrm{Beta}(x + \alpha, n - x + \beta)$, so $P(H_1 \mid d) = F_{(x+\alpha, n-x+\beta)}(\theta)$ and $P(H_0 \mid d) = 1 - F_{(x+\alpha, n-x+\beta)}(\theta)$. Bayes' theorem gives $\mathcal B_n = \frac{P(H_0 \mid d)}{P(H_1 \mid d)} \cdot \frac{P(H_1)}{P(H_0)}$, which is the stated formula; no numerical integration is needed. For the error bound, stopping with $\mathcal B_n > T$ means the data are at least $T$ times likelier under $H_0$; summing over all stopping sequences that accept $H_0$, their total probability under $H_1$ is at most $1/T$ times their probability under $H_0$, hence at most $1/T$ (and symmetrically for wrongly accepting $H_1$). In the pathway application, properties of an HMGB1 signaling-pathway model were verified with $T = 1000$, so each decision has error probability at most $10^{-3}$.

## Sources

- H. Gong, P. Zuliani, A. Komuravelli, J. R. Faeder, E. M. Clarke, "Analysis and verification of the HMGB1 signaling pathway", *BMC Bioinformatics* 11 (Suppl 7) (2010) S10. Methods, "Bounded Linear Temporal Logic (BLTL)" and "Statistical Model Checking" (Eqs. (1)–(8), Proposition 1, Theorem); Results, statistical model checking with threshold $T = 1000$. <https://doi.org/10.1186/1471-2105-11-s7-s10>. PMCID: PMC2957678.
