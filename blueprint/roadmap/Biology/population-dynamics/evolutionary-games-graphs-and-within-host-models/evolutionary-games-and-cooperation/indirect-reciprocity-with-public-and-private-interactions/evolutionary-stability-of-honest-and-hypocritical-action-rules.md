# Evolutionary stability of honest and hypocritical action rules

**Model.** In an infinitely large population, random pairs are formed of a donor and a recipient. The donor either cooperates (cost $c$ to the donor, benefit $b > c$ to the recipient) or defects (no cost, no benefit). Each interaction is public with probability $p$ and private with probability $1-p$; a public interaction is always observed, a private one with probability $q$, so an interaction is observed with probability

$$\bar q = p + (1-p)\,q .$$

Every player carries a binary reputation (good or bad) on which everyone agrees. An **action rule** is a four-letter word over $\{C, D\}$ giving the donor's move against a good recipient in public, a bad recipient in public, a good recipient in private, and a bad recipient in private; there are $16$ rules. When an interaction is observed, the donor's new reputation is set by a common **second-order social norm**, a map from (action, recipient's reputation, public or private) to {good, bad}; there are $256$ norms. Reputations equilibrate on a faster time scale than selection acts on action rules.

**Theorem.** Across all $256$ norms:

- unconditional defection $DDDD$ is an evolutionarily stable strategy (ESS) under every norm;
- if $b/c < \bar q/q$ and $b/c < \bar q/p$, then $DDDD$ is the only ESS;
- if $b/c > \bar q/p$, the hypocritical rule $CDDD$ (cooperate with good recipients only in public) is an ESS under suitable norms;
- if $b/c > \bar q/q$, the honest rule $CDCD$ (cooperate with good recipients, defect against bad ones, in both settings) is an ESS under suitable norms, namely combinations of the Simple Standing, Stern Judging and Shunning assessments;
- if $b/c > \bar q/[(1-p)q]$, the rule $CCCD$ is an ESS under suitable norms, and if $b/c > \bar q/(pq)$, the rule $CDCC$ is an ESS under suitable norms.

Since $\bar q/q = 1 + p(1-q)/q < 1/q$ for $p < 1$ and $q < 1$, the honest rule is stabilized at a lower benefit-to-cost ratio than the threshold $b/c > 1/q$ of models in which observers are always present but recipients' reputations are remembered only with probability $q$.

## Proof sketch

Stability is checked by dynamic programming: in a resident population playing a given rule, compute the value $v$ of holding a good rather than a bad reputation, then check that every letter of the rule is a best response given $v$. For the honest rule the dangerous mutant is the hypocrite. Consider a good donor meeting a good recipient in private. Cooperating costs $c$ and preserves the good reputation. Defecting saves $c$ but, with probability $q$, earns a bad reputation; a bad player receives no help (losing $b$ per interaction as recipient) until an observed good act restores the reputation, which takes on average $1/\bar q$ interactions. Defection therefore costs $qb/\bar q$ in expectation, and cooperation is the better reply exactly when $c < qb/\bar q$, that is $b/c > \bar q/q$. The other thresholds arise in the same way from the corresponding most dangerous deviations. Under the Scoring norm (cooperation good, defection bad) the honest rule is not an ESS (apart from the degenerate case $v = c$), because cooperation and defection then cannot both be best responses against good and bad recipients. Multiple ESS can coexist; when $1 < b/c < 2$ there is a region of $(p,q)$ in which no rule other than $DDDD$ is stable.

## Sources

- H. Ohtsuki, Y. Iwasa and M. A. Nowak, "Reputation effects in public and private interactions", PLoS Computational Biology 11 (2015), e1004527, Models and Results (ESS thresholds and supporting norms, Figs. 2–3; derivations in S1 Text), <https://doi.org/10.1371/journal.pcbi.1004527>, PMCID PMC4659694.
