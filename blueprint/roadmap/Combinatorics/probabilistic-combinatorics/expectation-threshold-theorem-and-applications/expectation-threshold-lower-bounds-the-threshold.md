# The expectation threshold is a lower bound on the threshold

For every nontrivial increasing family $\mathcal{F}$: if $\mathcal{F}$ is $p$-small then $\mu_p(\mathcal{F}) \le 1/2$, hence $q(\mathcal{F}) \le p_c(\mathcal{F})$.

## Proof sketch

If $\mathcal{G}$ covers $\mathcal{F}$ with $\sum_G p^{|G|} \le 1/2$, then $\mu_p(\mathcal{F}) \le \mu_p(\langle\mathcal{G}\rangle) \le \sum_G \mu_p(\{W : W \supseteq G\}) = \sum_G p^{|G|} \le 1/2$, by the union bound; since $\mu_p(\mathcal{F})$ is increasing in $p$ and equals $1/2$ at $p_c$, $p \le p_c$.

## Depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)

## Sources

- Jeff Kahn, Gil Kalai, "Thresholds and expectation thresholds", Combinatorics, Probability and Computing 16(3) (2007).
