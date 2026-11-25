# Bilateral trade impossibility (dominant-strategy form)

Consider one seller with private cost $s \in [0,1]$ and one buyer with private value $b \in [0,1]$. A direct mechanism maps reports
$(s, b)$ to a trade probability $x(s, b) \in [0, 1]$ and payments, the buyer paying $p_b(s, b)$ and the seller receiving $p_s(s, b)$;
utilities are quasilinear, $b\, x - p_b$ for the buyer and $p_s - s\, x$ for the seller, and both outside options are $0$. No mechanism is
simultaneously dominant-strategy incentive compatible for both agents, ex post individually rational, weakly budget balanced
($p_b \ge p_s$ at every pair of reports) and ex post efficient (trade with probability $1$ when $b > s$ and $0$ when $b < s$). This
dominant-strategy statement is distinct from the Bayesian [Myerson–Satterthwaite theorem](myerson-satterthwaite.md), whose hypotheses are
Bayesian incentive compatibility, interim individual rationality and continuous positive densities on overlapping intervals.

Proof sketch. For a fixed cost $s$, the buyer faces a single-parameter mechanism whose allocation is $1$ for $b > s$ and $0$ for $b < s$, so
by Myerson's lemma $p_b(s, b) = s + h(s)$ for $b > s$, where $-h(s)$ is the buyer's utility at the values $b < s$, and individual
rationality there gives $h(s) \le 0$. In the same way $p_s(s, b) = b + g(b)$ for $s < b$, where $g(b)$ is the seller's utility at the costs
$s > b$, so $g(b) \ge 0$. For $0 < s < b < 1$ this gives $p_b(s, b) \le s < b \le p_s(s, b)$, contradicting weak budget balance.

## Depends on

- [Dominant-strategy incentive compatibility](revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Myerson's lemma](myerson-s-lemma-and-revenue-equivalence/is-incentive-compatible-on-iff.md)

## Related topics

- [Myerson–Satterthwaite theorem](myerson-satterthwaite.md)
- [Truthful utility](myerson-s-lemma-and-revenue-equivalence/truthful-utility.md)
- [Incentive compatibility on an interval](myerson-s-lemma-and-revenue-equivalence/is-incentive-compatible-on.md)

## Sources

- K. Goldner, DS 574 Algorithmic Mechanism Design, Lecture 15 (two-sided markets), Boston University, Fall 2025: Definition 2 (bilateral trade), the utilities and weak budget balance, and Theorem 1, which states that already for one buyer and one seller the allocation maximizing gains from trade need not be implementable by any dominant-strategy incentive compatible, ex post individually rational, weakly budget balanced mechanism. The interval model and the proof sketch above are the elementary argument from Myerson's lemma. <https://www.kiragoldner.com/teaching/DS574/fall25/L15.pdf>
