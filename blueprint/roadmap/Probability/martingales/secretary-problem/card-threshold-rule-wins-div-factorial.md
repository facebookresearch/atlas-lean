# Win probability of a threshold rule in the random-order model

Let $1 \le r \le n$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$, read $\sigma(i)$ as the
quality of the applicant interviewed at time $i$. The rule $N_r$ rejects the applicants
interviewed at times $0, \dots, r - 2$ and selects the first later applicant who is best so far.
Then the proportion of permutations for which $N_r$ selects the best applicant of all equals the
[win probability](win-prob.md) $P_r$.

The proof follows Ferguson's derivation: the rule wins exactly when the best applicant comes at a time $k \ge r - 1$ and the best of the first $k$ applicants comes before time $r - 1$, which has probability $\frac{1}{n} \cdot \frac{r-1}{k}$ for $k \ge r \ge 2$ (and $\frac1n$ for $k = r - 1$). Both uniformities are proved by exchanging two positions, a bijection of the permutations: the position of the best applicant is uniform on $\{0, \dots, n-1\}$, and given that it is $k \ge 1$, the position of the best of the first $k$ applicants is uniform on $\{0, \dots, k-1\}$.

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics), Chapter 2, §2.1, equation (3) and its derivation.
