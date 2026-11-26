# Expected IBD per generation and the IBDNe moment update

Keep the setting of [the posterior TMRCA of an observed IBD segment](posterior-tmrca-of-an-observed-ibd-segment.md): diploid sizes $N[g]$, Haldane crossovers, segments retained only if their observed length exceeds a threshold $C$ cM, TMRCA $\ge g^\ast$. Let $n_P$ be the number of haplotype pairs from distinct individuals ($n_P = 2n_I(2n_I - 2)/2$ for $n_I$ diploids), and let the genome consist of $K$ chromosomes of lengths $L_1, \dots, L_K$ cM with every $L_k > C$. A chromosome with $L_k \le C$ carries no segment longer than $C$, so it contributes nothing to $X_g$ and is omitted from the sums in both $E_g$ and $Y_g$ (the bracket below would wrongly give it a positive contribution, e.g. $C$ when $L_k = C$).

**Expected amount (Eq. A5).** The expected total length of IBD with TMRCA $g$ and observed length $> C$ is

$$E_g(N) = n_P \Bigl(\prod_{g'=g^\ast}^{g-1}\Bigl(1 - \frac{1}{2N[g']}\Bigr)\Bigr) \frac{1}{2N[g]}\, e^{-Cg/50} \sum_{k=1}^{K}\Bigl\{\Bigl(\frac{Cg}{50} + 1\Bigr)L_k - \frac{C^2 g}{50}\Bigr\}.$$

**Observed amount (Eq. A3).** The observed IBD attributed to generation $g$ is $X_g = \sum_j l^{(j)} P(\mathrm{TMRCA} = g \mid s_1^{(j)}, s_2^{(j)}, N)$, summed over observed segments $j$ with length $l^{(j)} > C$.

**Update (Eq. A6).** Writing $E_g(N) = Y_g / N[g]$, equating $X_g = E_g$ with $N[g^\ast], \dots, N[g-1]$ held at their current values gives

$$\hat N[g] = \frac{Y_g}{X_g}, \qquad Y_g = n_P \Bigl(\prod_{g'=g^\ast}^{g-1}\Bigl(1 - \frac{1}{2N[g']}\Bigr)\Bigr) \frac{1}{2}\, e^{-Cg/50}\sum_{k}\Bigl\{\Bigl(\frac{Cg}{50} + 1\Bigr)L_k - \frac{C^2 g}{50}\Bigr\}.$$

With a piecewise-exponential constraint on an interval $g_1 \le g \le g_2$, one sets $N[g] = N[g_2 + 1]\, e^{r(g_2 + 1 - g)}$ (Eq. A7) and solves $\sum_{g=g_1}^{g_2} X_g = \sum_{g=g_1}^{g_2} Y_g / N[g]$ for $r$ by Newton's method, working from the oldest interval (where a constant $N = \sum Y_g / \sum X_g$ is fitted) toward the present.

## Proof sketch

A segment covering a fixed point has Erlang-2 length with rate $g/50$, so $P(l > C \mid \mathrm{TMRCA} = g) = (Cg/50 + 1)e^{-Cg/50}$. Integrating over positions of a chromosome of length $L$ and over $n_P$ pairs gives $n_P L\, P(l > C, \mathrm{TMRCA} = g)$ (Eq. A4) when censoring is ignored. Near an end, a segment through a point $h < C$ whose right end $s_2$ lies before $C$ is observed shorter than $C$ although its conceptual length may exceed $C$. The probability of that event is $\int_h^C (g/50) e^{-(s_2 - h)g/50} e^{-(h - s_2 + C)g/50}\, ds_2 = (C - h)(g/50) e^{-Cg/50}$, and integrating over $0 < h < C$ yields $C^2 g\, e^{-Cg/50}/100$ per end. Subtracting twice that gives the bracket in $E_g$; the result is exact for every $L_k > C$ (direct integration of $P(\min(A, x) + \min(B, L_k - x) > C)$ over positions $x$, with independent $\mathrm{Exp}(g/50)$ extents $A, B$, gives the same bracket also when $C < L_k < 2C$), whereas a chromosome with $L_k \le C$ contributes $0$, not the bracket. The map $N \mapsto \hat N$ is a generalized EM step that uses method-of-moments in place of the M-step. IBDNe iterates it from random autoregressive starting trajectories, averages the runs harmonically (since $\hat N[g] \propto 1/X_g$), and bootstraps over chromosomes for intervals.

## Depends on

- [Posterior TMRCA of an observed IBD segment](posterior-tmrca-of-an-observed-ibd-segment.md)

## Sources

- S. R. Browning and B. L. Browning, "Accurate non-parametric estimation of recent effective population size from segments of identity by descent", American Journal of Human Genetics 97 (2015), 404–418, Methods ("Overview of Estimation Procedure", "Averaging Results from Multiple Random Starts") and Appendix A ("Expected Amount of IBD from Generation g", "Updating the Estimate of Historical Effective Population Size N[g]", Equations A3–A7), <https://doi.org/10.1016/j.ajhg.2015.07.012>, PMCID PMC4564943.
